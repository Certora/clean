/-
  Port of `MenhirLib/Validator_complete.v`: the completeness validator.

  The automaton is *complete* with respect to the grammar when the item
  annotations (`items_of_state`), the nullable and first annotations are
  consistent with the grammar and with the action and goto tables.
  `is_complete` is the executable validator; `complete_is_validator` proves it
  sound.

  Differences from Rocq: the AVL sets of terminals are bit masks (`ASet`), and
  instead of building an AVL map of all the items, `find_items_map` reads the
  items of the given state directly (`items_of_state` is indexed by states
  already).  The validators are written explicitly instead of being derived
  from type-class instances.
-/
import CCLib.MenhirLib.Automaton
import CCLib.MenhirLib.Validator_classes

namespace CC
namespace MenhirLib

section Complete
variable [Alphs] [GrammarT] [AutInit] [AutomatonT]

/-- Sets of terminals. -/
abbrev TerminalSet := ASet terminal

/-- Nullable predicate for symbols and lists of symbols. -/
def nullable_symb : Symbol → Bool
  | .NT nt => nullable_nterm nt
  | _ => false

def nullable_word (word : List Symbol) : Bool := word.all nullable_symb

/-- First predicate for non terminals, symbols and lists of symbols. -/
def first_nterm_set (nterm : nonterminal) : TerminalSet := ASet.ofList (first_nterm nterm)

def first_symb_set : Symbol → TerminalSet
  | .NT nt => first_nterm_set nt
  | .T t => ASet.singleton t

def first_word_set : List Symbol → TerminalSet
  | [] => ASet.empty
  | t :: q => if nullable_symb t then ASet.union (first_symb_set t) (first_word_set q)
    else first_symb_set t

omit [AutInit] in
/-- The part of a production after the dot. -/
def future_of_prod (prod : production) (dot_pos : Nat) : List Symbol :=
  (prod_rhs_rev prod).reverse.drop dot_pos

omit [AutInit] [AutomatonT] in
theorem future_of_prod_succ {prod : production} {pos : Nat} {s : Symbol} {q : List Symbol}
    (h : future_of_prod prod pos = s :: q) : future_of_prod prod (pos + 1) = q := by
  unfold future_of_prod at *
  rw [← List.tail_drop, h]; rfl

/-- The lookaheads of the items of `state` with production `prod` and dot
position `dot_pos` (Rocq's `find_items_map (items_map ())`). -/
def find_items_map (state : State) (prod : production) (dot_pos : Nat) : TerminalSet :=
  (items_of_state state).foldl (fun acc it =>
    if it.prod_item = prod ∧ it.dot_pos_item = dot_pos then
      ASet.union (ASet.ofList it.lookaheads_item) acc
    else acc) ASet.empty

theorem in_find_items_map_iff (state : State) (prod : production) (dot_pos : Nat)
    (la : terminal) :
    ASet.In la (find_items_map state prod dot_pos) ↔
      ∃ it ∈ items_of_state state, it.prod_item = prod ∧ it.dot_pos_item = dot_pos ∧
        la ∈ it.lookaheads_item := by
  unfold find_items_map
  have key : ∀ (l : List item) (acc : TerminalSet),
      ASet.In la (l.foldl (fun acc it =>
        if it.prod_item = prod ∧ it.dot_pos_item = dot_pos then
          ASet.union (ASet.ofList it.lookaheads_item) acc
        else acc) acc) ↔
      (∃ it ∈ l, it.prod_item = prod ∧ it.dot_pos_item = dot_pos ∧ la ∈ it.lookaheads_item) ∨
        ASet.In la acc := by
    intro l
    induction l with
    | nil => intro acc; simp
    | cons it l ih =>
      intro acc
      rw [List.foldl_cons, ih]
      split
      · rename_i h
        rw [ASet.in_union_iff, ASet.in_ofList_iff]
        constructor
        · rintro (⟨it', hit', h'⟩ | h' | h')
          · exact Or.inl ⟨it', List.mem_cons_of_mem _ hit', h'⟩
          · exact Or.inl ⟨it, List.mem_cons_self, h.1, h.2, h'⟩
          · exact Or.inr h'
        · rintro (⟨it', hit', h'⟩ | h')
          · rcases List.mem_cons.1 hit' with rfl | hit'
            · exact Or.inr (Or.inl h'.2.2)
            · exact Or.inl ⟨it', hit', h'⟩
          · exact Or.inr (Or.inr h')
      · rename_i h
        constructor
        · rintro (⟨it', hit', h'⟩ | h')
          · exact Or.inl ⟨it', List.mem_cons_of_mem _ hit', h'⟩
          · exact Or.inr h'
        · rintro (⟨it', hit', h'⟩ | h')
          · rcases List.mem_cons.1 hit' with rfl | hit'
            · exact absurd ⟨h'.1, h'.2.1⟩ h
            · exact Or.inl (⟨it', hit', h'⟩)
          · exact Or.inr h'
  rw [key]
  have := ASet.not_in_empty la
  constructor
  · rintro (h | h)
    · exact h
    · exact absurd h this
  · exact Or.inl

/-- The state `state` has an item for production `prod` whose future is `fut`
and whose lookaheads contain `lookahead`. -/
def state_has_future (state : State) (prod : production) (fut : List Symbol)
    (lookahead : terminal) : Prop :=
  ∃ dot_pos : Nat, fut = future_of_prod prod dot_pos ∧
    ASet.In lookahead (find_items_map state prod dot_pos)

/-- Iterator over all the items of all the states. -/
def forallb_items (P : State → production → Nat → TerminalSet → Bool) : Bool :=
  (all_list : List State).all fun st => (items_of_state st).all fun it =>
    P st it.prod_item it.dot_pos_item (ASet.ofList it.lookaheads_item)

theorem forallb_items_spec {P : State → production → Nat → TerminalSet → Bool}
    (h : forallb_items P = true) {st : State} {prod : production} {fut : List Symbol}
    {lookahead : terminal} (hf : state_has_future st prod fut lookahead) :
    ∃ pos lset, fut = future_of_prod prod pos ∧ ASet.In lookahead lset ∧
      P st prod pos lset = true := by
  obtain ⟨pos, hfut, hin⟩ := hf
  obtain ⟨it, hit, hp, hpos, hla⟩ := (in_find_items_map_iff _ _ _ _).1 hin
  have := List.all_eq_true.1 (all_list_all_spec h st) it hit
  subst hp hpos
  exact ⟨_, _, hfut, (ASet.in_ofList_iff _ _).2 hla, this⟩

/-! ## Validation for completeness -/

/-- The nullable predicate is a fixpoint: it is correct. -/
def nullable_stable : Prop :=
  ∀ p : production, nullable_word (prod_rhs_rev p) = true → nullable_nterm (prod_lhs p) = true

/-- The first predicate is a fixpoint: it is correct. -/
def first_stable : Prop :=
  ∀ p : production,
    ASet.Subset (first_word_set (prod_rhs_rev p).reverse) (first_nterm_set (prod_lhs p))

/-- The initial state has all the `S → .u` items, where `S` is the start
non-terminal. -/
def start_future : Prop :=
  ∀ (init : initstate) (p : production), prod_lhs p = start_nt init →
    ∀ t : terminal, state_has_future (.Init init) p (prod_rhs_rev p).reverse t

/-- If a state contains an item of the form `A → _.av[[b]]`, where `a` is a
terminal, then reading an `a` does a `Shift_act` to a state containing an
item of the form `A → _.v[[b]]`. -/
def terminal_shift : Prop :=
  ∀ (s1 : State) prod fut lookahead, state_has_future s1 prod fut lookahead →
    match fut with
    | .T t :: q =>
      match action_table s1 with
      | .Lookahead_act awp =>
        match awp t with
        | .Shift_act s2 _ => state_has_future (.Ninit s2) prod q lookahead
        | _ => False
      | _ => False
    | _ => True

/-- If a state contains an item of the form `A → _.[[a]]`, then either we do a
`Default_reduce_act` of the corresponding production, or reading `a` does a
`Reduce_act` of the corresponding production. -/
def end_reduce : Prop :=
  ∀ (s : State) prod fut lookahead, state_has_future s prod fut lookahead →
    match fut with
    | [] =>
      match action_table s with
      | .Default_reduce_act p => p = prod
      | .Lookahead_act awt =>
        match awt lookahead with
        | .Reduce_act p => p = prod
        | _ => False
    | _ => True

/-- If a state contains an item of the form `A → _.Bv[[b]]`, where `B` is a
non terminal, then the goto table says we have to go to a state containing an
item of the form `A → _.v[[b]]`. -/
def non_terminal_goto : Prop :=
  ∀ (s1 : State) prod fut lookahead, state_has_future s1 prod fut lookahead →
    match fut with
    | .NT nt :: q =>
      match goto_table s1 nt with
      | some ⟨s2, _⟩ => state_has_future (.Ninit s2) prod q lookahead
      | none => False
    | _ => True

def start_goto : Prop :=
  ∀ init : initstate, goto_table (.Init init) (start_nt init) = none

/-- Closure property of item sets: if a state contains an item of the form
`A → _.Bv[[b]]`, then for each production `B → u` and each terminal `a` of
`first(vb)`, the state contains an item of the form `B → _.u[[a]]`. -/
def non_terminal_closed : Prop :=
  ∀ (s1 : State) prod fut lookahead, state_has_future s1 prod fut lookahead →
    match fut with
    | .NT nt :: q =>
      ∀ p, prod_lhs p = nt →
        (nullable_word q = true → state_has_future s1 p (future_of_prod p 0) lookahead) ∧
        (∀ lookahead2, ASet.In lookahead2 (first_word_set q) →
          state_has_future s1 p (future_of_prod p 0) lookahead2)
    | _ => True

/-- The automaton is complete. -/
def complete : Prop :=
  nullable_stable ∧ first_stable ∧ start_future ∧ terminal_shift ∧ end_reduce ∧
  non_terminal_goto ∧ start_goto ∧ non_terminal_closed

/-! ## The executable validator -/

def is_nullable_stable : Bool :=
  (all_list : List production).all fun p =>
    !nullable_word (prod_rhs_rev p) || nullable_nterm (prod_lhs p)

def is_first_stable : Bool :=
  (all_list : List production).all fun p =>
    ASet.subset (first_word_set (prod_rhs_rev p).reverse) (first_nterm_set (prod_lhs p))

def is_start_future : Bool :=
  (all_list : List initstate).all fun init => (all_list : List production).all fun p =>
    !decide (prod_lhs p = start_nt init) ||
    (all_list : List terminal).all fun t => ASet.mem t (find_items_map (.Init init) p 0)

def is_terminal_shift : Bool :=
  forallb_items fun s prod pos lset =>
    match future_of_prod prod pos with
    | .T t :: _ =>
      match action_table s with
      | .Lookahead_act awp =>
        match awp t with
        | .Shift_act s2 _ => ASet.subset lset (find_items_map (.Ninit s2) prod (pos + 1))
        | _ => false
      | _ => false
    | _ => true

def is_end_reduce : Bool :=
  forallb_items fun s prod pos lset =>
    match future_of_prod prod pos with
    | [] =>
      match action_table s with
      | .Default_reduce_act p => decide (p = prod)
      | .Lookahead_act awt =>
        (all_list : List terminal).all fun la => !ASet.mem la lset ||
          match awt la with
          | .Reduce_act p => decide (p = prod)
          | _ => false
    | _ => true

def is_non_terminal_goto : Bool :=
  forallb_items fun s prod pos lset =>
    match future_of_prod prod pos with
    | .NT nt :: _ =>
      match goto_table s nt with
      | some ⟨s2, _⟩ => ASet.subset lset (find_items_map (.Ninit s2) prod (pos + 1))
      | none => false
    | _ => true

def is_start_goto : Bool :=
  (all_list : List initstate).all fun init => (goto_table (.Init init) (start_nt init)).isNone

def is_non_terminal_closed : Bool :=
  forallb_items fun s prod pos lset =>
    match future_of_prod prod pos with
    | .NT nt :: q =>
      (all_list : List production).all fun p => !decide (prod_lhs p = nt) ||
        ((!nullable_word q || ASet.subset lset (find_items_map s p 0)) &&
          ASet.subset (first_word_set q) (find_items_map s p 0))
    | _ => true

/-- The completeness validator (Rocq's derived `is_complete`). -/
def is_complete (_ : Unit) : Bool :=
  is_nullable_stable && is_first_stable && is_start_future && is_terminal_shift &&
  is_end_reduce && is_non_terminal_goto && is_start_goto && is_non_terminal_closed

theorem nullable_stable_of (h : is_nullable_stable = true) : nullable_stable := by
  intro p hp
  have := all_list_all_spec h p
  rw [hp] at this
  simpa using this

theorem first_stable_of (h : is_first_stable = true) : first_stable :=
  fun p => ASet.subset_spec (all_list_all_spec h p)

theorem start_future_of (h : is_start_future = true) : start_future := by
  intro init p hp t
  have := all_list_all_spec (all_list_all_spec h init) p
  simp only [hp, decide_true, Bool.not_true, Bool.false_or] at this
  exact ⟨0, rfl, all_list_all_spec this t⟩

theorem terminal_shift_of (h : is_terminal_shift = true) : terminal_shift := by
  intro s1 prod fut la hf
  obtain ⟨pos, lset, rfl, hla, hchk⟩ := forallb_items_spec h hf
  revert hchk
  generalize hfut : future_of_prod prod pos = fut
  match fut with
  | [] => intro _; trivial
  | .NT _ :: _ => intro _; trivial
  | .T t :: q =>
    simp only
    cases action_table s1 with
    | Default_reduce_act _ => intro hchk; exact Bool.false_ne_true hchk
    | Lookahead_act awp =>
      simp only
      cases awp t with
      | Shift_act s2 _ =>
        intro hchk
        exact ⟨pos + 1, (future_of_prod_succ hfut).symm, ASet.subset_spec hchk la hla⟩
      | Reduce_act _ => intro hchk; exact Bool.false_ne_true hchk
      | Fail_act => intro hchk; exact Bool.false_ne_true hchk

theorem end_reduce_of (h : is_end_reduce = true) : end_reduce := by
  intro s prod fut la hf
  obtain ⟨pos, lset, rfl, hla, hchk⟩ := forallb_items_spec h hf
  revert hchk
  generalize future_of_prod prod pos = fut
  match fut with
  | _ :: _ => intro _; trivial
  | [] =>
    simp only
    cases action_table s with
    | Default_reduce_act p => intro hchk; exact of_decide_eq_true hchk
    | Lookahead_act awt =>
      simp only
      intro hchk
      have := all_list_all_spec hchk la
      have hm : ASet.mem la lset = true := hla
      simp only [hm, Bool.not_true, Bool.false_or] at this
      revert this
      cases awt la with
      | Reduce_act p => exact of_decide_eq_true
      | Shift_act _ _ => exact Bool.false_ne_true
      | Fail_act => exact Bool.false_ne_true

theorem non_terminal_goto_of (h : is_non_terminal_goto = true) : non_terminal_goto := by
  intro s1 prod fut la hf
  obtain ⟨pos, lset, rfl, hla, hchk⟩ := forallb_items_spec h hf
  revert hchk
  generalize hfut : future_of_prod prod pos = fut
  match fut with
  | [] => intro _; trivial
  | .T _ :: _ => intro _; trivial
  | .NT nt :: q =>
    simp only
    cases goto_table s1 nt with
    | none => exact Bool.false_ne_true
    | some x =>
      obtain ⟨s2, _⟩ := x
      intro hchk
      exact ⟨pos + 1, (future_of_prod_succ hfut).symm, ASet.subset_spec hchk la hla⟩

theorem start_goto_of (h : is_start_goto = true) : start_goto := by
  intro init
  exact Option.isNone_iff_eq_none.1 (all_list_all_spec h init)

theorem non_terminal_closed_of (h : is_non_terminal_closed = true) : non_terminal_closed := by
  intro s1 prod fut la hf
  obtain ⟨pos, lset, rfl, hla, hchk⟩ := forallb_items_spec h hf
  revert hchk
  generalize future_of_prod prod pos = fut
  match fut with
  | [] => intro _; trivial
  | .T _ :: _ => intro _; trivial
  | .NT nt :: q =>
    simp only
    intro hchk p hp
    have := all_list_all_spec hchk p
    simp only [hp, decide_true, Bool.not_true, Bool.false_or, Bool.and_eq_true] at this
    refine ⟨fun hn => ?_, fun la2 hla2 => ?_⟩
    · rw [hn, Bool.not_true, Bool.false_or] at this
      exact ⟨0, rfl, ASet.subset_spec this.1 la hla⟩
    · exact ⟨0, rfl, ASet.subset_spec this.2 la2 hla2⟩

theorem complete_is_validator : IsValidator complete (is_complete ()) := by
  intro h
  simp only [is_complete, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨nullable_stable_of h1, first_stable_of h2, start_future_of h3, terminal_shift_of h4,
    end_reduce_of h5, non_terminal_goto_of h6, start_goto_of h7, non_terminal_closed_of h8⟩

end Complete

end MenhirLib
end CC
