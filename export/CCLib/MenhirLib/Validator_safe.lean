/-
  Port of `MenhirLib/Validator_safe.v`: the safety validator.

  The automaton is *safe* when the annotations (`past_symb_of_non_init_state`,
  `past_state_of_non_init_state`) are consistent with the action and goto
  tables, so that the interpreter never pops a symbol that is not on the
  stack and always finds a goto after a reduction.  `is_safe` is the
  executable validator; `safe_is_validator` proves it sound.

  Rocq's `prefix` relation is core's `List.IsPrefix` (`<+:`) here, and its
  validator `is_prefix` is `List.isPrefixOf`.
-/
import CCLib.MenhirLib.Automaton
import CCLib.MenhirLib.Validator_classes

namespace CC
namespace MenhirLib

section Safe
variable [Alphs] [GrammarT] [AutInit] [AutomatonT]

/-- The singleton predicate for states. -/
def singleton_state_pred (state : State) : State → Bool := fun state' => decide (state = state')

omit [AutomatonT] in
theorem singleton_state_pred_refl (s : State) : singleton_state_pred s s = true := by
  simp [singleton_state_pred]

/-- `past_state_of_non_init_state`, extended to all states. -/
def past_state_of_state : State → List (State → Bool)
  | .Init _ => []
  | .Ninit nis => past_state_of_non_init_state nis

/-- Concatenation of the last and the past symbols. -/
def head_symbs_of_state : State → List Symbol
  | .Init _ => []
  | .Ninit s => last_symb_of_non_init_state s :: past_symb_of_non_init_state s

def head_states_of_state (state : State) : List (State → Bool) :=
  singleton_state_pred state :: past_state_of_state state

/-- If we shift, then the known top symbols of the destination state are a
prefix of the known top symbols of the source state. -/
def shift_head_symbs : Prop :=
  ∀ s, match action_table s with
    | .Lookahead_act awp => ∀ t, match awp t with
      | .Shift_act s2 _ => past_symb_of_non_init_state s2 <+: head_symbs_of_state s
      | _ => True
    | _ => True

/-- When a goto happens, the known top symbols of the destination state are a
prefix of the known top symbols of the source state. -/
def goto_head_symbs : Prop :=
  ∀ s nt, match goto_table s nt with
    | some ⟨s2, _⟩ => past_symb_of_non_init_state s2 <+: head_symbs_of_state s
    | none => True

/-- "Prefix" over lists of predicates on states: each predicate of the first
list is implied by the corresponding predicate of the second one. -/
inductive prefix_pred : List (State → Bool) → List (State → Bool) → Prop where
  | nil (l) : prefix_pred [] l
  | cons (l1 l2 f1 f2) : (∀ x, (!f2 x || f1 x) = true) →
      prefix_pred l1 l2 → prefix_pred (f1 :: l1) (f2 :: l2)

omit [AutomatonT] in
theorem prefix_pred_trans {l1 l2 l3 : List (State → Bool)}
    (h1 : prefix_pred l1 l2) (h2 : prefix_pred l2 l3) : prefix_pred l1 l3 := by
  induction h1 generalizing l3 with
  | nil => exact .nil _
  | cons l1 l2 f1 f2 hf _ ih =>
    cases h2 with
    | cons _ l3 _ f3 hf3 h2 =>
      refine .cons _ _ _ _ (fun x => ?_) (ih h2)
      have a := hf x
      have b := hf3 x
      revert a b
      cases f1 x <;> cases f2 x <;> cases f3 x <;> simp

def is_prefix_pred : List (State → Bool) → List (State → Bool) → Bool
  | [], _ => true
  | f1 :: q1, f2 :: q2 =>
    (all_list : List State).all (fun x => (!f2 x || f1 x)) && is_prefix_pred q1 q2
  | _ :: _, [] => false

omit [AutomatonT] in
theorem prefix_pred_is_validator (l1 l2 : List (State → Bool)) :
    IsValidator (prefix_pred l1 l2) (is_prefix_pred l1 l2) := by
  induction l1 generalizing l2 with
  | nil => intro _; exact .nil _
  | cons f1 l1 ih =>
    cases l2 with
    | nil => intro h; simp [is_prefix_pred] at h
    | cons f2 l2 =>
      intro h
      simp only [is_prefix_pred, Bool.and_eq_true] at h
      exact .cons _ _ _ _ (all_list_all_spec h.1) (ih l2 h.2)

/-- The assumptions about the state stack are preserved by a shift. -/
def shift_past_state : Prop :=
  ∀ s, match action_table s with
    | .Lookahead_act awp => ∀ t, match awp t with
      | .Shift_act s2 _ =>
        prefix_pred (past_state_of_non_init_state s2) (head_states_of_state s)
      | _ => True
    | _ => True

/-- The assumptions about the state stack are preserved by a goto. -/
def goto_past_state : Prop :=
  ∀ s nt, match goto_table s nt with
    | some ⟨s2, _⟩ => prefix_pred (past_state_of_non_init_state s2) (head_states_of_state s)
    | none => True

/-- What states are possible after having popped these symbols from the
stack, given the annotation of the current state? -/
inductive state_valid_after_pop (s : State) : List Symbol → List (State → Bool) → Prop where
  | nil1 (p pl) : p s = true → state_valid_after_pop s [] (p :: pl)
  | nil2 (sl) : state_valid_after_pop s sl []
  | cons (st sq p pl) : state_valid_after_pop s sq pl →
      state_valid_after_pop s (st :: sq) (p :: pl)

def is_state_valid_after_pop (state : State) : List Symbol → List (State → Bool) → Bool
  | _, [] => true
  | [], p :: _ => p state
  | _ :: sl, _ :: pl => is_state_valid_after_pop state sl pl

omit [AutomatonT] in
theorem is_state_valid_after_pop_complete {state : State} {sl pl}
    (h : state_valid_after_pop state sl pl) : is_state_valid_after_pop state sl pl = true := by
  induction h with
  | nil1 p pl hp => exact hp
  | nil2 sl => cases sl <;> rfl
  | cons st sq p pl _ ih => exact ih

/-- A state is valid for reducing a production when the right hand side of
the production is on the stack, and a goto is possible after popping it. -/
def valid_for_reduce (state : State) (prod : production) : Prop :=
  prod_rhs_rev prod <+: head_symbs_of_state state ∧
  ∀ state_new, state_valid_after_pop state_new (prod_rhs_rev prod) (head_states_of_state state) →
    match goto_table state_new (prod_lhs prod) with
    | none => match state_new with
      | .Init i => prod_lhs prod = start_nt i
      | .Ninit _ => False
    | some _ => True

/-- All the states that reduce are valid for this reduction. -/
def reduce_ok : Prop :=
  ∀ s, match action_table s with
    | .Lookahead_act awp => ∀ t, match awp t with
      | .Reduce_act p => valid_for_reduce s p
      | _ => True
    | .Default_reduce_act p => valid_for_reduce s p

/-- The automaton is safe. -/
def safe : Prop :=
  shift_head_symbs ∧ goto_head_symbs ∧ shift_past_state ∧ goto_past_state ∧ reduce_ok

/-! ## The executable validator -/

def is_shift_head_symbs : Bool :=
  (all_list : List State).all fun s => match action_table s with
    | .Lookahead_act awp => (all_list : List terminal).all fun t => match awp t with
      | .Shift_act s2 _ => (past_symb_of_non_init_state s2).isPrefixOf (head_symbs_of_state s)
      | _ => true
    | _ => true

def is_goto_head_symbs : Bool :=
  (all_list : List State).all fun s => (all_list : List nonterminal).all fun nt =>
    match goto_table s nt with
    | some ⟨s2, _⟩ => (past_symb_of_non_init_state s2).isPrefixOf (head_symbs_of_state s)
    | none => true

def is_shift_past_state : Bool :=
  (all_list : List State).all fun s => match action_table s with
    | .Lookahead_act awp => (all_list : List terminal).all fun t => match awp t with
      | .Shift_act s2 _ =>
        is_prefix_pred (past_state_of_non_init_state s2) (head_states_of_state s)
      | _ => true
    | _ => true

def is_goto_past_state : Bool :=
  (all_list : List State).all fun s => (all_list : List nonterminal).all fun nt =>
    match goto_table s nt with
    | some ⟨s2, _⟩ => is_prefix_pred (past_state_of_non_init_state s2) (head_states_of_state s)
    | none => true

def is_valid_for_reduce (state : State) (prod : production) : Bool :=
  (prod_rhs_rev prod).isPrefixOf (head_symbs_of_state state) &&
  (all_list : List State).all fun state_new =>
    !is_state_valid_after_pop state_new (prod_rhs_rev prod) (head_states_of_state state) ||
    match goto_table state_new (prod_lhs prod) with
    | none => match state_new with
      | .Init i => decide (prod_lhs prod = start_nt i)
      | .Ninit _ => false
    | some _ => true

/-- The productions reduced by a lookahead action table (each production is
checked once, not once per terminal). -/
def reduced_prods (awp : ∀ t : terminal, lookahead_action t) : List production :=
  ((all_list : List terminal).filterMap fun t => match awp t with
    | .Reduce_act p => some p
    | _ => none).eraseDups

def is_reduce_ok : Bool :=
  (all_list : List State).all fun s => match action_table s with
    | .Lookahead_act awp => (reduced_prods awp).all (is_valid_for_reduce s)
    | .Default_reduce_act p => is_valid_for_reduce s p

/-- The safety validator (Rocq's derived `is_safe`). -/
def is_safe (_ : Unit) : Bool :=
  is_shift_head_symbs && is_goto_head_symbs && is_shift_past_state && is_goto_past_state &&
  is_reduce_ok

theorem is_valid_for_reduce_spec {s : State} {p : production}
    (h : is_valid_for_reduce s p = true) : valid_for_reduce s p := by
  simp only [is_valid_for_reduce, Bool.and_eq_true] at h
  refine ⟨List.isPrefixOf_iff_prefix.1 h.1, fun state_new hsv => ?_⟩
  have h2 := all_list_all_spec h.2 state_new
  rw [is_state_valid_after_pop_complete hsv] at h2
  simp only [Bool.not_true, Bool.false_or] at h2
  revert h2
  cases goto_table state_new (prod_lhs p) with
  | some _ => intro _; trivial
  | none =>
    cases state_new with
    | Init i => intro h2; exact of_decide_eq_true h2
    | Ninit _ => intro h2; exact Bool.false_ne_true h2

theorem safe_is_validator : IsValidator safe (is_safe ()) := by
  intro h
  simp only [is_safe, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨fun s => ?_, fun s nt => ?_, fun s => ?_, fun s nt => ?_, fun s => ?_⟩
  · have := all_list_all_spec h1 s
    revert this
    cases action_table s with
    | Default_reduce_act _ => intro _; trivial
    | Lookahead_act awp =>
      intro h t
      have := all_list_all_spec h t
      revert this
      cases awp t with
      | Shift_act s2 _ => exact List.isPrefixOf_iff_prefix.1
      | _ => intro _; trivial
  · have := all_list_all_spec (all_list_all_spec h2 s) nt
    revert this
    cases goto_table s nt with
    | some x => exact List.isPrefixOf_iff_prefix.1
    | none => intro _; trivial
  · have := all_list_all_spec h3 s
    revert this
    cases action_table s with
    | Default_reduce_act _ => intro _; trivial
    | Lookahead_act awp =>
      intro h t
      have := all_list_all_spec h t
      revert this
      cases awp t with
      | Shift_act s2 _ => exact prefix_pred_is_validator _ _
      | _ => intro _; trivial
  · have := all_list_all_spec (all_list_all_spec h4 s) nt
    revert this
    cases goto_table s nt with
    | some x => exact prefix_pred_is_validator _ _
    | none => intro _; trivial
  · have := all_list_all_spec h5 s
    revert this
    cases action_table s with
    | Default_reduce_act p => exact is_valid_for_reduce_spec
    | Lookahead_act awp =>
      intro h t
      have hmem : ∀ p, awp t = .Reduce_act p → p ∈ reduced_prods awp := by
        intro p hp
        rw [reduced_prods, List.mem_eraseDups, List.mem_filterMap]
        exact ⟨t, all_list_forall t, by rw [hp]⟩
      revert hmem
      cases awp t with
      | Reduce_act p =>
        intro hmem
        exact is_valid_for_reduce_spec (List.all_eq_true.1 h p (hmem p rfl))
      | _ => intro _; trivial

end Safe

end MenhirLib
end CC
