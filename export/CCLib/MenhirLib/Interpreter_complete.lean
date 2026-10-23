/-
  Port of `MenhirLib/Interpreter_complete.v`: completeness of the interpreter.

  For every parse tree of a word, the parser run on this word followed by any
  input returns the semantic value of the tree and the rest of the input when
  it has enough fuel, times out otherwise, and never fails.

  The dotted parse trees used in the proof are in
  `Interpreter_completeZipper.lean`.  This file relates them to the stack of
  the parser (`ptd_stack_compat`) and shows that each step of the parser
  follows `next_ptd`.
-/
import CCLib.MenhirLib.Interpreter_completeZipper
import CCLib.MenhirLib.Validator_complete

namespace CC
namespace MenhirLib

section Completeness
variable [Alphs] [GrammarT] [AutInit] [AutomatonT]

/-! ### Correctness of the nullable and first annotations -/

section Annotations

mutual
/-- If the nullable predicate has been validated, then it is correct. -/
theorem nullable_correct (Hcomplete : complete) : {head : Symbol} → {word : List token} →
    parse_tree head word → word = [] → nullable_symb head = true
  | _, _, .Terminal_pt _, h => absurd h (List.cons_ne_nil _ _)
  | _, _, .Non_terminal_pt prod ptl, h => Hcomplete.1 prod (nullable_correct_list Hcomplete ptl h)

theorem nullable_correct_list (Hcomplete : complete) : {heads : List Symbol} → {word : List token} →
    parse_tree_list heads word → word = [] → nullable_word heads = true
  | _, _, .Nil_ptl, _ => rfl
  | _, _, .Cons_ptl q t, h => by
    rw [List.append_eq_nil_iff] at h
    simp only [nullable_word, List.all_cons, Bool.and_eq_true]
    exact ⟨nullable_correct Hcomplete t h.2, nullable_correct_list Hcomplete q h.1⟩
end

theorem first_word_set_app (t : terminal) (word1 word2 : List Symbol) :
    ASet.In t (first_word_set (word1 ++ word2)) ↔
      ASet.In t (first_word_set word1) ∨
      (ASet.In t (first_word_set word2) ∧ nullable_word word1 = true) := by
  induction word1 with
  | nil =>
    have := ASet.not_in_empty t
    simp only [List.nil_append, first_word_set, nullable_word, List.all_nil, and_true]
    exact ⟨Or.inr, fun h => h.elim (fun h' => absurd h' this) id⟩
  | cons s word1 ih =>
    simp only [List.cons_append, first_word_set, nullable_word, List.all_cons]
    cases nullable_symb s with
    | true =>
      simp only [ite_true, ASet.in_union_iff, ih, Bool.true_and]
      constructor
      · rintro (h | h | h)
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
      · rintro ((h | h) | h)
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
    | false =>
      simp only [Bool.false_eq_true, ite_false, Bool.false_and, and_false, or_false]

mutual
/-- If the first predicate has been validated, then it is correct. -/
theorem first_correct (Hcomplete : complete) : {head : Symbol} → {word : List token} →
    parse_tree head word → ∀ t q, word = t :: q → ASet.In (token_term t) (first_symb_set head)
  | _, _, .Terminal_pt tok, t, q, h => by
    simp only [List.cons.injEq] at h
    rw [h.1]
    exact (ASet.in_singleton_iff _ _).2 rfl
  | _, _, .Non_terminal_pt prod ptl, t, q, h =>
    Hcomplete.2.1 prod _ (first_correct_list Hcomplete ptl t q h)

theorem first_correct_list (Hcomplete : complete) : {heads : List Symbol} → {word : List token} →
    parse_tree_list heads word → ∀ t q, word = t :: q →
      ASet.In (token_term t) (first_word_set heads.reverse)
  | _, _, .Nil_ptl, _, _, h => absurd h.symm (List.cons_ne_nil _ _)
  | _, _, .Cons_ptl (wordq := wordq) ptl pt, t, q, h => by
    rw [List.reverse_cons, first_word_set_app]
    match wordq, ptl, h with
    | [], ptl, h =>
      right
      refine ⟨?_, ?_⟩
      · simp only [first_word_set]
        have := first_correct Hcomplete pt t q h
        cases nullable_symb _
        · exact this
        · exact (ASet.in_union_iff _ _ _).2 (Or.inl this)
      · have := nullable_correct_list Hcomplete ptl rfl
        simpa [nullable_word, List.all_reverse] using this
    | t' :: q', ptl, h =>
      left
      simp only [List.cons_append, List.cons.injEq] at h
      rw [← h.1]
      exact first_correct_list Hcomplete ptl t' q' rfl
end

end Annotations

/-! ### Compatibility of parse trees and stacks -/

/-- A list of parse trees is compatible with a stack if the top of the stack
contains data representing it, above `stk0`. -/
def ptl_stack_compat (stk0 : Stack) : {symbs : List Symbol} → {word : List token} →
    parse_tree_list symbs word → Stack → Prop
  | _, _, .Nil_ptl, stk => stk0 = stk
  | _, _, .Cons_ptl (head_symbolt := sym) ptl pt, stk =>
    match stk with
    | [] => False
    | ⟨s, sem⟩ :: stk =>
      ptl_stack_compat stk0 ptl stk ∧
      ∃ e : sym = last_symb_of_non_init_state s,
        sem = cast (congrArg symbol_semantic_type e) (pt_sem pt)

omit [AutomatonT] in
theorem ptl_stack_compat_nil (stk : Stack) : ∀ {symbs : List Symbol} {word : List token}
    (ptl : parse_tree_list symbs word), symbs = [] → ptl_stack_compat stk ptl stk
  | _, _, .Nil_ptl, _ => rfl
  | _, _, .Cons_ptl _ _, h => absurd h (List.cons_ne_nil _ _)

omit [AutomatonT] in
/-- When a list of parse trees is compatible with a stack, `pop` returns its
semantic value. -/
theorem pop_stack_compat {A : Type} (stk0 : Stack) : ∀ {symbs : List Symbol} {word : List token}
    (ptl : parse_tree_list symbs word) (stk : Stack)
    (action : arrows_right A (symbs.map symbol_semantic_type)),
    ptl_stack_compat stk0 ptl stk → ∀ hp, pop symbs stk hp action = (stk0, ptl_sem ptl action)
  | _, _, .Nil_ptl, stk, action, h, hp => by
    simp only [ptl_stack_compat] at h
    subst h
    simp [pop]
  | _, _, .Cons_ptl ptl pt, [], action, h, hp => by simp [ptl_stack_compat] at h
  | _, _, .Cons_ptl ptl pt, ⟨s, sem⟩ :: stk, action, h, hp => by
    obtain ⟨h1, e, rfl⟩ := h
    subst e
    simp only [pop, ptl_sem_Cons_ptl]
    exact pop_stack_compat stk0 ptl stk _ h1 _


/-! ### The invariant: compatibility of dotted parse trees and stacks -/

section Invariant
variable {init : initstate} {full_word : List token} (buffer_end : Buffer)

/-- The production being recognised at the hole of a zipper. -/
def ptlz_prod : {hole_symbs : List Symbol} → {hole_word : List token} →
    ptl_zipper init full_word hole_symbs hole_word → production
  | _, _, .Non_terminal_pt_ptlz (p := prod) _ => prod
  | _, _, .Cons_ptl_ptlz _ ptlz' => ptlz_prod ptlz'

/-- The symbols of this production after the hole. -/
def ptlz_future : {hole_symbs : List Symbol} → {hole_word : List token} →
    ptl_zipper init full_word hole_symbs hole_word → List Symbol
  | _, _, .Non_terminal_pt_ptlz _ => []
  | _, _, .Cons_ptl_ptlz (head_symbolt := s) _ ptlz' => s :: ptlz_future ptlz'

/-- The lookahead terminal of the item of this production. -/
def ptlz_lookahead : {hole_symbs : List Symbol} → {hole_word : List token} →
    ptl_zipper init full_word hole_symbs hole_word → terminal
  | _, _, .Non_terminal_pt_ptlz ptz => token_term (buf_head (ptz_buffer buffer_end ptz))
  | _, _, .Cons_ptl_ptlz _ ptlz' => ptlz_lookahead ptlz'

mutual
/-- A stack is compatible with a zipper when it is the concatenation of stack
fragments compatible with each of the partially recognised productions, and
the head of each fragment has an item predicted by the zipper. -/
def ptz_stack_compat : Stack → {hole_symb : Symbol} → {hole_word : List token} →
    pt_zipper init full_word hole_symb hole_word → Prop
  | stk, _, _, .Top_ptz => stk = []
  | stk, hole_symb, _, .Cons_ptl_ptz ptl ptlz =>
    ∃ stk0,
      state_has_future (state_of_stack init stk) (ptlz_prod ptlz)
        (hole_symb :: ptlz_future ptlz) (ptlz_lookahead buffer_end ptlz) ∧
      ptl_stack_compat stk0 ptl stk ∧
      ptlz_stack_compat stk0 ptlz

def ptlz_stack_compat : Stack → {hole_symbs : List Symbol} → {hole_word : List token} →
    ptl_zipper init full_word hole_symbs hole_word → Prop
  | stk, _, _, .Non_terminal_pt_ptlz ptz => ptz_stack_compat stk ptz
  | stk, _, _, .Cons_ptl_ptlz _ ptlz => ptlz_stack_compat stk ptlz
end

/-- The main invariant of the completeness proof. -/
def ptd_stack_compat : pt_dot init full_word → Stack → Prop
  | .Reduce_ptd (prod := prod) ptl ptz, stk =>
    ∃ stk0,
      state_has_future (state_of_stack init stk) prod []
        (token_term (buf_head (ptz_buffer buffer_end ptz))) ∧
      ptl_stack_compat stk0 ptl stk ∧
      ptz_stack_compat buffer_end stk0 ptz
  | .Shift_ptd tok ptl ptlz, stk =>
    ∃ stk0,
      state_has_future (state_of_stack init stk) (ptlz_prod ptlz)
        (.T (token_term tok) :: ptlz_future ptlz) (ptlz_lookahead buffer_end ptlz) ∧
      ptl_stack_compat stk0 ptl stk ∧
      ptlz_stack_compat buffer_end stk0 ptlz

theorem ptlz_future_ptlz_prod : {hole_symbs : List Symbol} → {hole_word : List token} →
    (ptlz : ptl_zipper init full_word hole_symbs hole_word) →
    (ptlz_future ptlz).reverse ++ hole_symbs = prod_rhs_rev (ptlz_prod ptlz)
  | _, _, .Non_terminal_pt_ptlz _ => by simp [ptlz_future, ptlz_prod]
  | _, _, .Cons_ptl_ptlz _ ptlz' => by
    simp only [ptlz_future, ptlz_prod, List.reverse_cons, List.append_assoc, List.singleton_append]
    exact ptlz_future_ptlz_prod ptlz'

theorem ptlz_future_first (Hcomplete : complete) : {symbs : List Symbol} → {word : List token} →
    (ptlz : ptl_zipper init full_word symbs word) →
    ASet.In (token_term (buf_head (ptlz_buffer buffer_end ptlz)))
      (first_word_set (ptlz_future ptlz)) ∨
    (token_term (buf_head (ptlz_buffer buffer_end ptlz)) = ptlz_lookahead buffer_end ptlz ∧
      nullable_word (ptlz_future ptlz) = true)
  | _, _, .Non_terminal_pt_ptlz ptz => by
    right; simp [ptlz_future, ptlz_lookahead, ptlz_buffer, nullable_word]
  | _, _, .Cons_ptl_ptlz (wordt := wordt) pt ptlz => by
    match wordt, pt, ptlz with
    | [], pt, ptlz =>
      have hn := nullable_correct Hcomplete pt rfl
      have ih := ptlz_future_first Hcomplete ptlz
      simp only [ptlz_buffer, app_buf, ptlz_future, ptlz_lookahead, first_word_set, hn,
        ite_true, nullable_word, List.all_cons, Bool.true_and] at ih ⊢
      rcases ih with h | h
      · exact Or.inl ((ASet.in_union_iff _ _ _).2 (Or.inr h))
      · exact Or.inr h
    | tok :: q, pt, ptlz =>
      left
      have := first_correct Hcomplete pt tok q rfl
      simp only [ptlz_buffer, app_buf, buf_head_cons, ptlz_future, first_word_set]
      split
      · exact (ASet.in_union_iff _ _ _).2 (Or.inl this)
      · exact this

end Invariant


/-! ### `next_ptd` preserves the invariant -/

section BuildCompat
variable {init : initstate} {full_word : List token} (buffer_end : Buffer)

/-- The state on top of a stack compatible with the zipper of a reduction of
`prod` has an item `prod → .rhs`. -/
theorem ptz_stack_compat_future (Hcomplete : complete) : {symb : Symbol} → {word : List token} →
    (ptz : pt_zipper init full_word symb word) → (stk : Stack) →
    ptz_stack_compat buffer_end stk ptz → (prod : production) → symb = .NT (prod_lhs prod) →
    state_has_future (state_of_stack init stk) prod (prod_rhs_rev prod).reverse
      (token_term (buf_head (ptz_buffer buffer_end ptz)))
  | _, _, .Top_ptz, stk, hz, prod, hs => by
    simp only [ptz_stack_compat] at hz
    subst hz
    injection hs with hs
    exact Hcomplete.2.2.1 init prod hs.symm _
  | _, _, .Cons_ptl_ptz ptl0 ptlz0, stk, hz, prod, hs => by
    subst hs
    obtain ⟨stk0, hfut, _, _⟩ := hz
    have hc := Hcomplete.2.2.2.2.2.2.2 _ _ _ _ hfut prod rfl
    rcases ptlz_future_first buffer_end Hcomplete ptlz0 with hf | ⟨hf, hn⟩
    · exact hc.2 _ hf
    · have := hc.1 hn
      rw [← hf] at this
      exact this

mutual
theorem ptd_stack_compat_build_from_pt (Hcomplete : complete) : {symb : Symbol} → {word : List token} →
    (pt : parse_tree symb word) → (ptz : pt_zipper init full_word symb word) → (stk : Stack) →
    ptz_stack_compat buffer_end stk ptz →
    ptd_stack_compat buffer_end (build_pt_dot_from_pt pt ptz) stk
  | _, _, .Terminal_pt tok, .Cons_ptl_ptz ptl ptlz, stk, hz => by
    simp only [build_pt_dot_from_pt, ptd_stack_compat]
    exact hz
  | _, _, .Non_terminal_pt prod ptl, ptz, stk, hz => by
    have hfut := ptz_stack_compat_future buffer_end Hcomplete ptz stk hz prod rfl
    by_cases h : prod_rhs_rev prod = []
    · simp only [build_pt_dot_from_pt, h, dite_true, ptd_stack_compat]
      rw [h] at hfut
      exact ⟨stk, hfut, ptl_stack_compat_nil stk ptl h, hz⟩
    · rw [build_pt_dot_from_pt, dif_neg h]
      exact ptd_stack_compat_build_from_pt_rec Hcomplete ptl _ stk h hz hfut

theorem ptd_stack_compat_build_from_pt_rec (Hcomplete : complete) : {symbs : List Symbol} → {word : List token} →
    (ptl : parse_tree_list symbs word) → (ptlz : ptl_zipper init full_word symbs word) →
    (stk : Stack) → (h : symbs ≠ []) →
    ptlz_stack_compat buffer_end stk ptlz →
    state_has_future (state_of_stack init stk) (ptlz_prod ptlz)
      (prod_rhs_rev (ptlz_prod ptlz)).reverse (ptlz_lookahead buffer_end ptlz) →
    ptd_stack_compat buffer_end (build_pt_dot_from_pt_rec ptl h ptlz) stk
  | _, _, .Nil_ptl, _, _, h, _, _ => absurd rfl h
  | _, _, .Cons_ptl .Nil_ptl pt, ptlz, stk, _, hz, hfut => by
    rw [build_pt_dot_from_pt_rec]
    refine ptd_stack_compat_build_from_pt Hcomplete pt _ stk ⟨stk, ?_, rfl, hz⟩
    rw [← ptlz_future_ptlz_prod ptlz] at hfut
    simpa using hfut
  | _, _, .Cons_ptl (.Cons_ptl ptl'' pt'') pt, ptlz, stk, _, hz, hfut => by
    rw [build_pt_dot_from_pt_rec]
    exact ptd_stack_compat_build_from_pt_rec Hcomplete _ _ stk _ hz hfut
end

theorem ptd_stack_compat_build_from_ptl (Hcomplete : complete) : {symbs : List Symbol} → {word : List token} →
    (ptl : parse_tree_list symbs word) → (ptlz : ptl_zipper init full_word symbs word) →
    (stk stk0 : Stack) →
    ptlz_stack_compat buffer_end stk0 ptlz → ptl_stack_compat stk0 ptl stk →
    state_has_future (state_of_stack init stk) (ptlz_prod ptlz) (ptlz_future ptlz)
      (ptlz_lookahead buffer_end ptlz) →
    ptd_stack_compat buffer_end (build_pt_dot_from_ptl ptl ptlz) stk
  | _, _, ptl, .Non_terminal_pt_ptlz ptz, stk, stk0, hz, hl, hfut => by
    simp only [build_pt_dot_from_ptl, ptd_stack_compat]
    exact ⟨stk0, hfut, hl, hz⟩
  | _, _, ptl, .Cons_ptl_ptlz pt ptlz, stk, stk0, hz, hl, hfut => by
    rw [build_pt_dot_from_ptl]
    exact ptd_stack_compat_build_from_pt buffer_end Hcomplete pt _ stk ⟨stk0, hfut, hl, hz⟩

end BuildCompat


/-! ### Each step of the parser follows `next_ptd` -/

section Steps
variable {init : initstate} {full_word : List token} (buffer_end : Buffer)
  (Hcomplete : complete)
include Hcomplete

/-- After a reduction followed by a goto, the parser follows `next_ptd`. -/
theorem goto_next_ptd : {symb : Symbol} → {word : List token} →
    (ptz : pt_zipper init full_word symb word) → (pt : parse_tree symb word) → (stk0 : Stack) →
    ptz_stack_compat buffer_end stk0 ptz → (nt : nonterminal) → (hs : symb = .NT nt) →
    (sn : noninitstate) → (e : Symbol.NT nt = last_symb_of_non_init_state sn) →
    goto_table (state_of_stack init stk0) nt = some ⟨sn, e⟩ →
    ∃ ptd, next_of_ptz ptz pt = some ptd ∧
      ptd_buffer buffer_end ptd = ptz_buffer buffer_end ptz ∧
      ptd_stack_compat buffer_end ptd
        (⟨sn, cast (congrArg symbol_semantic_type (hs.trans e)) (pt_sem pt)⟩ :: stk0)
  | _, _, .Top_ptz, _, stk0, hz, nt, hs, sn, e, hg => by
    simp only [ptz_stack_compat] at hz
    subst hz
    injection hs with hs
    have := Hcomplete.2.2.2.2.2.2.1 init
    rw [hs] at this
    simp only [state_of_stack] at hg
    rw [this] at hg
    cases hg
  | _, _, .Cons_ptl_ptz ptl' ptlz, pt, stk0, hz, nt, hs, sn, e, hg => by
    subst hs
    obtain ⟨stk0', hfut, hl, hz'⟩ := hz
    refine ⟨_, rfl, ?_, ?_⟩
    · rw [← ptd_buffer_build_from_ptl]
      simp [ptz_buffer]
    · apply ptd_stack_compat_build_from_ptl buffer_end Hcomplete _ ptlz _ stk0' hz'
      · simp only [ptl_stack_compat]
        exact ⟨hl, e, rfl⟩
      · have := Hcomplete.2.2.2.2.2.1 _ _ _ _ hfut
        simp only at this
        rw [hg] at this
        exact this

/-- After a reduction without goto, the parser accepts. -/
theorem accept_next_ptd : {symb : Symbol} → {word : List token} →
    (ptz : pt_zipper init full_word symb word) → (pt : parse_tree symb word) →
    ptz_stack_compat buffer_end [] ptz → (nt : nonterminal) → symb = .NT nt →
    goto_table (.Init init) nt = none →
    ∃ e : symb = .NT (start_nt init), next_of_ptz ptz pt = none ∧
      ptz_buffer buffer_end ptz = buffer_end ∧
      ptz_sem ptz (pt_sem pt) = cast (congrArg symbol_semantic_type e) (pt_sem pt)
  | _, _, .Top_ptz, pt, _, _, _, _ => ⟨rfl, by simp [next_of_ptz], by simp [ptz_buffer],
      by simp [ptz_sem]⟩
  | _, _, .Cons_ptl_ptz ptl' ptlz, pt, hz, nt, hs, hg => by
    subst hs
    obtain ⟨stk0', hfut, _, _⟩ := hz
    have := Hcomplete.2.2.2.2.2.1 _ _ _ _ hfut
    simp only [state_of_stack] at this
    rw [hg] at this
    exact this.elim

/-- The reduction steps follow `next_ptd`. -/
theorem reduce_step_next_ptd (prod : production) (word : List token)
    (ptl : parse_tree_list (prod_rhs_rev prod) word)
    (ptz : pt_zipper init full_word (.NT (prod_lhs prod)) word) (stk : Stack)
    (Hval : valid_for_reduce (state_of_stack init stk) prod) (Hi : stack_invariant init stk) :
    ptd_stack_compat buffer_end (.Reduce_ptd ptl ptz) stk →
    match next_ptd (.Reduce_ptd ptl ptz) with
    | none => reduce_step stk prod (ptz_buffer buffer_end ptz) Hval Hi =
        .Accept_sr (ptd_sem (.Reduce_ptd ptl ptz)) buffer_end
    | some ptd => ∃ stk', reduce_step stk prod (ptz_buffer buffer_end ptz) Hval Hi =
        .Progress_sr stk' (ptd_buffer buffer_end ptd) ∧ ptd_stack_compat buffer_end ptd stk' := by
  rintro ⟨stk0, _, hl, hz⟩
  have hpop := pop_stack_compat stk0 ptl stk (prod_action prod) hl (reduce_pop_ok Hval Hi)
  show match next_of_ptz ptz (.Non_terminal_pt prod ptl) with
    | none => _ | some ptd => _
  rcases reduce_step_spec stk prod (ptz_buffer buffer_end ptz) Hval Hi with
    ⟨sn, e, hg, hr⟩ | ⟨e, hg, hnil, hr⟩
  · rw [hpop] at hg hr
    obtain ⟨ptd, hn, hb, hc⟩ :=
      goto_next_ptd buffer_end Hcomplete ptz (.Non_terminal_pt prod ptl) stk0 hz (prod_lhs prod)
        rfl sn e hg
    rw [hn]
    refine ⟨_, ?_, hc⟩
    rw [hr, hb, pt_sem_Non_terminal_pt]
  · rw [hpop] at hg hr hnil
    simp only at hnil
    subst hnil
    obtain ⟨e', hn, hb, hs⟩ :=
      accept_next_ptd buffer_end Hcomplete ptz (.Non_terminal_pt prod ptl) hz (prod_lhs prod) rfl hg
    rw [hn]
    show _ = _
    rw [hr, hb]
    simp only [ptd_sem]
    rw [← pt_sem_Non_terminal_pt, hs]

variable (Hsafe : safe)

/-- Each step of the parser follows `next_ptd`. -/
theorem step_next_ptd (ptd : pt_dot init full_word) (stk : Stack) (Hi : stack_invariant init stk) :
    ptd_stack_compat buffer_end ptd stk →
    match next_ptd ptd with
    | none => step init Hsafe stk (ptd_buffer buffer_end ptd) Hi =
        .Accept_sr (ptd_sem ptd) buffer_end
    | some ptd' => ∃ stk', step init Hsafe stk (ptd_buffer buffer_end ptd) Hi =
        .Progress_sr stk' (ptd_buffer buffer_end ptd') ∧ ptd_stack_compat buffer_end ptd' stk' := by
  intro Hstk
  match ptd with
  | .Reduce_ptd (prod := prod) ptl ptz =>
    have hfut := Hstk.choose_spec.1
    have hact := Hcomplete.2.2.2.2.1 _ _ _ _ hfut
    simp only at hact
    rcases step_spec init Hsafe stk (ptd_buffer buffer_end (.Reduce_ptd ptl ptz)) Hi with
      ⟨p, Hv, ha, hs⟩ | ⟨awt, sn, e, ha, hl, hs⟩ | ⟨awt, p, Hv, ha, hl, hs⟩ | ⟨awt, ha, hl, hs⟩
    · rw [ha] at hact
      simp only at hact
      subst p
      rw [hs]
      exact reduce_step_next_ptd buffer_end Hcomplete _ _ ptl ptz stk Hv Hi Hstk
    · rw [ha] at hact
      simp only [ptd_buffer] at hl
      simp only at hact
      rw [hl] at hact
      simp only at hact
    · rw [ha] at hact
      simp only [ptd_buffer] at hl
      simp only at hact
      rw [hl] at hact
      simp only at hact
      subst p
      rw [hs]
      exact reduce_step_next_ptd buffer_end Hcomplete _ _ ptl ptz stk Hv Hi Hstk
    · rw [ha] at hact
      simp only [ptd_buffer] at hl
      simp only at hact
      rw [hl] at hact
      simp only at hact
  | .Shift_ptd tok ptl ptlz =>
    obtain ⟨stk0, hfut, hl0, hz⟩ := Hstk
    have hact := Hcomplete.2.2.2.1 _ _ _ _ hfut
    simp only at hact
    rcases step_spec init Hsafe stk (ptd_buffer buffer_end (.Shift_ptd tok ptl ptlz)) Hi with
      ⟨p, Hv, ha, hs⟩ | ⟨awt, sn, e, ha, hl, hs⟩ | ⟨awt, p, Hv, ha, hl, hs⟩ | ⟨awt, ha, hl, hs⟩
    · rw [ha] at hact
      exact hact.elim
    · rw [ha] at hact
      simp only [ptd_buffer, buf_head_cons] at hl hs
      simp only at hact
      rw [hl] at hact
      simp only at hact
      simp only [next_ptd]
      refine ⟨⟨sn, cast (congrArg symbol_semantic_type e) (token_sem tok)⟩ :: stk, ?_, ?_⟩
      · refine hs.trans ?_
        rw [← ptd_buffer_build_from_ptl]
        rfl
      · apply ptd_stack_compat_build_from_ptl buffer_end Hcomplete _ ptlz _ stk0 hz
        · exact ⟨hl0, e, by rw [pt_sem_Terminal_pt]; rfl⟩
        · exact hact
    · rw [ha] at hact
      simp only [ptd_buffer, buf_head_cons] at hl
      simp only at hact
      rw [hl] at hact
      simp only at hact
    · rw [ha] at hact
      simp only [ptd_buffer, buf_head_cons] at hl
      simp only at hact
      rw [hl] at hact
      simp only at hact

/-- The main loop of the parser follows `next_ptd_iter`. -/
theorem parse_fix_next_ptd_iter (log_n_steps : Nat) : ∀ (ptd : pt_dot init full_word)
    (stk : Stack) (Hi : stack_invariant init stk),
    ptd_stack_compat buffer_end ptd stk →
    match next_ptd_iter ptd log_n_steps with
    | none => (parse_fix init Hsafe stk (ptd_buffer buffer_end ptd) log_n_steps Hi).1 =
        .Accept_sr (ptd_sem ptd) buffer_end
    | some ptd' => ∃ stk', (parse_fix init Hsafe stk (ptd_buffer buffer_end ptd) log_n_steps Hi).1 =
        .Progress_sr stk' (ptd_buffer buffer_end ptd') ∧ ptd_stack_compat buffer_end ptd' stk' := by
  induction log_n_steps with
  | zero => exact step_next_ptd buffer_end Hcomplete Hsafe
  | succ n ih =>
    intro ptd stk Hi Hstk
    have ih1 := ih ptd stk Hi Hstk
    have hsem := sem_next_ptd_iter ptd n
    simp only [parse_fix, next_ptd_iter]
    revert ih1 hsem
    rcases parse_fix init Hsafe stk (ptd_buffer buffer_end ptd) n Hi with ⟨sr, Hi'⟩
    cases next_ptd_iter ptd n with
    | none =>
      intro h _
      simp only at h
      subst h
      rfl
    | some ptd1 =>
      rintro ⟨stk', h, hc⟩ hsem
      simp only at h
      subst h
      have := ih ptd1 stk' (Hi' _ _ rfl) hc
      rw [hsem ptd1 rfl]
      exact this

end Steps

/-! ### Completeness of the parser -/

/-- Completeness theorem: for every parse tree of a word, the parser run on
this word followed by any input returns the semantic value of the tree and the
rest of the input if it has enough fuel, times out otherwise, and never
fails. -/
theorem parse_complete (init : initstate) (Hsafe : safe) (Hcomplete : complete)
    (full_word : List token) (buffer_end : Buffer)
    (full_pt : parse_tree (.NT (start_nt init)) full_word) (log_n_steps : Nat) :
    match parse init Hsafe (app_buf full_word buffer_end) log_n_steps with
    | .Parsed_pr sem buff =>
      sem = pt_sem full_pt ∧ buff = buffer_end ∧ pt_size full_pt ≤ 2 ^ log_n_steps
    | .Timeout_pr => 2 ^ log_n_steps < pt_size full_pt
    | .Fail_pr_full _ _ => False := by
  have Hstk : ptd_stack_compat buffer_end (build_pt_dot_from_pt full_pt (.Top_ptz (init := init)
      (full_word := full_word))) [] :=
    ptd_stack_compat_build_from_pt buffer_end Hcomplete full_pt _ [] rfl
  have Hparse := parse_fix_next_ptd_iter buffer_end Hcomplete Hsafe log_n_steps _ []
    (stack_invariant_nil init) Hstk
  have hbuf := ptd_buffer_build_from_pt buffer_end full_pt
    (.Top_ptz (init := init) (full_word := full_word))
  have hsem := sem_build_from_pt full_pt (.Top_ptz (init := init) (full_word := full_word))
  have Hcost := next_ptd_iter_cost (build_pt_dot_from_pt full_pt
    (.Top_ptz (init := init) (full_word := full_word))) log_n_steps
  have hc := ptd_cost_build_from_pt full_pt (.Top_ptz (init := init) (full_word := full_word))
  simp only [ptz_buffer] at hbuf
  simp only [ptz_sem] at hsem
  simp only [ptz_cost] at hc
  unfold parse
  revert Hparse Hcost
  cases next_ptd_iter (build_pt_dot_from_pt full_pt .Top_ptz) log_n_steps with
  | none =>
    intro Hparse Hcost
    simp only at Hparse Hcost
    rw [← hbuf] at Hparse
    rw [Hparse]
    exact ⟨hsem.symm, rfl, by omega⟩
  | some ptd' =>
    rintro ⟨stk', h, _⟩ Hcost
    rw [← hbuf] at h
    rw [h]
    simp only at Hcost ⊢
    omega

end Completeness

end MenhirLib
end CC
