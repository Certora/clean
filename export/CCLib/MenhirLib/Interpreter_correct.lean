/-
  Port of `MenhirLib/Interpreter_correct.v`: correctness of the interpreter.

  If the interpreter accepts, returning a semantic value, then this is the
  semantic value of a parse tree of a prefix of the input.
-/
import CCLib.MenhirLib.Interpreter

namespace CC
namespace MenhirLib

section Correct
variable [Alphs] [GrammarT] [AutInit] [AutomatonT]

/-- `word_has_stack_semantics word stack`: the word is a concatenation of
words that have the semantic values stored in the stack. -/
inductive word_has_stack_semantics : List token → Stack → Prop where
  | nil : word_has_stack_semantics [] []
  | cons {wordq : List token} {stackq : Stack} :
      word_has_stack_semantics wordq stackq →
      ∀ (wordt : List token) (s : noninitstate)
        (pt : parse_tree (last_symb_of_non_init_state s) wordt),
      word_has_stack_semantics (wordq ++ wordt) (⟨s, pt_sem pt⟩ :: stackq)

omit [AutomatonT] in
/-- `pop` preserves the invariant, and returns the semantic value of a list
of parse trees. -/
theorem pop_ptl (symbols_to_pop : List Symbol) {A : Type} (stk : Stack) hp
    (action : arrows_right A (symbols_to_pop.map symbol_semantic_type)) (word_stk : List token)
    (hw : word_has_stack_semantics word_stk stk) :
    ∃ word_stk' word_res, ∃ ptl : parse_tree_list symbols_to_pop word_res,
      word_stk' ++ word_res = word_stk ∧
      word_has_stack_semantics word_stk' (pop symbols_to_pop stk hp action).1 ∧
      ptl_sem ptl action = (pop symbols_to_pop stk hp action).2 := by
  induction symbols_to_pop generalizing stk word_stk with
  | nil => exact ⟨word_stk, [], .Nil_ptl, List.append_nil _, by simpa [pop] using hw, by simp [pop]⟩
  | cons t q ih =>
    cases hw with
    | nil => exact absurd hp (by simp [symb_stack_of_stack])
    | cons hw' wordt s pt =>
      have e := (List.cons_prefix_cons.1 hp).1
      subst e
      obtain ⟨w1, w2, ptl, hw12, hw1, hsem⟩ := ih _ _ (action (pt_sem pt)) _ hw'
      refine ⟨w1, w2 ++ wordt, .Cons_ptl ptl pt, ?_, ?_, ?_⟩
      · rw [← List.append_assoc, hw12]
      · simpa [pop] using hw1
      · simpa [pop, ptl_sem] using hsem

omit [AutInit] [AutomatonT] in
/-- Transporting a parse tree along an equality of symbols casts its semantic
value. -/
theorem pt_sem_cast {a b : Symbol} (e : a = b) {w : List token} (pt : parse_tree a w) :
    pt_sem (e ▸ pt) = cast (congrArg symbol_semantic_type e) (pt_sem pt) := by
  subst e; rfl

/-- `reduce_step` preserves the invariant. -/
theorem reduce_step_invariant (init : initstate) (stk : Stack) (prod : production)
    (Hv : valid_for_reduce (state_of_stack init stk) prod) (Hi : stack_invariant init stk)
    (word : List token) (buffer : Buffer) (hw : word_has_stack_semantics word stk) :
    match reduce_step stk prod buffer Hv Hi with
    | .Accept_sr sem buffer_new =>
      ∃ pt : parse_tree (.NT (start_nt init)) word, buffer = buffer_new ∧ pt_sem pt = sem
    | .Progress_sr stk' buffer_new => buffer = buffer_new ∧ word_has_stack_semantics word stk'
    | .Fail_sr_full _ _ => True := by
  obtain ⟨w1, w2, ptl, hw12, hw1, hsem⟩ :=
    pop_ptl (prod_rhs_rev prod) stk (reduce_pop_ok Hv Hi) (prod_action prod) word hw
  rcases reduce_step_spec stk prod buffer Hv Hi with ⟨state_new, e, _, hr⟩ | ⟨e, _, hnil, hr⟩
  · rw [hr]
    refine ⟨rfl, ?_⟩
    have := word_has_stack_semantics.cons hw1 w2 state_new (e ▸ .Non_terminal_pt prod ptl)
    rw [pt_sem_cast, pt_sem_Non_terminal_pt] at this
    rw [← hw12]
    exact (congrArg (fun x => word_has_stack_semantics (w1 ++ w2) (⟨state_new, cast _ x⟩ :: _))
      hsem) ▸ this
  · rw [hr]
    rw [hnil] at hw1
    cases hw1
    rw [List.nil_append] at hw12
    subst hw12
    refine ⟨congrArg Symbol.NT e ▸ .Non_terminal_pt prod ptl, rfl, ?_⟩
    rw [pt_sem_cast, pt_sem_Non_terminal_pt]
    exact congrArg (cast _) hsem

/-- `step` preserves the invariant. -/
theorem step_invariant (init : initstate) (Hsafe : safe) (stk : Stack) (word : List token)
    (buffer : Buffer) (Hi : stack_invariant init stk) (hw : word_has_stack_semantics word stk) :
    match step init Hsafe stk buffer Hi with
    | .Accept_sr sem buffer_new =>
      ∃ word_new, ∃ pt : parse_tree (.NT (start_nt init)) word_new,
        app_buf word buffer = app_buf word_new buffer_new ∧ pt_sem pt = sem
    | .Progress_sr stk_new buffer_new =>
      ∃ word_new, app_buf word buffer = app_buf word_new buffer_new ∧
        word_has_stack_semantics word_new stk_new
    | .Fail_sr_full _ _ => True := by
  have hred : ∀ prod Hv,
      match reduce_step stk prod buffer Hv Hi with
      | .Accept_sr sem buffer_new =>
        ∃ word_new, ∃ pt : parse_tree (.NT (start_nt init)) word_new,
          app_buf word buffer = app_buf word_new buffer_new ∧ pt_sem pt = sem
      | .Progress_sr stk_new buffer_new =>
        ∃ word_new, app_buf word buffer = app_buf word_new buffer_new ∧
          word_has_stack_semantics word_new stk_new
      | .Fail_sr_full _ _ => True := by
    intro prod Hv
    have := reduce_step_invariant init stk prod Hv Hi word buffer hw
    revert this
    cases reduce_step stk prod buffer Hv Hi with
    | Fail_sr_full _ _ => intro _; trivial
    | Accept_sr sem bn =>
      rintro ⟨pt, rfl, h⟩
      exact ⟨word, pt, rfl, h⟩
    | Progress_sr stk' bn =>
      rintro ⟨rfl, h⟩
      exact ⟨word, rfl, h⟩
  rcases step_spec init Hsafe stk buffer Hi with
    ⟨prod, Hv, _, hs⟩ | ⟨awt, state_new, e, _, _, hs⟩ | ⟨awt, prod, Hv, _, _, hs⟩ | ⟨awt, _, _, hs⟩
  · rw [hs]; exact hred prod Hv
  · rw [hs]
    refine ⟨word ++ [buf_head buffer], ?_, ?_⟩
    · rw [← app_buf_assoc]
      exact congrArg (app_buf word) (buf_cons_head_tail buffer).symm
    · have := word_has_stack_semantics.cons hw [buf_head buffer] state_new
        (e ▸ .Terminal_pt (buf_head buffer))
      rw [pt_sem_cast, pt_sem_Terminal_pt] at this
      exact this
  · rw [hs]; exact hred prod Hv
  · rw [hs]; trivial

/-- The main loop preserves the invariant. -/
theorem parse_fix_invariant (init : initstate) (Hsafe : safe) (log_n_steps : Nat) :
    ∀ (stk : Stack) (word : List token) (buffer : Buffer) (Hi : stack_invariant init stk),
    word_has_stack_semantics word stk →
    match (parse_fix init Hsafe stk buffer log_n_steps Hi).1 with
    | .Accept_sr sem buffer_new =>
      ∃ word_new, ∃ pt : parse_tree (.NT (start_nt init)) word_new,
        app_buf word buffer = app_buf word_new buffer_new ∧ pt_sem pt = sem
    | .Progress_sr stk_new buffer_new =>
      ∃ word_new, app_buf word buffer = app_buf word_new buffer_new ∧
        word_has_stack_semantics word_new stk_new
    | .Fail_sr_full _ _ => True := by
  induction log_n_steps with
  | zero =>
    intro stk word buffer Hi hw
    exact step_invariant init Hsafe stk word buffer Hi hw
  | succ n ih =>
    intro stk word buffer Hi hw
    have ih1 := ih stk word buffer Hi hw
    simp only [parse_fix]
    revert ih1
    rcases parse_fix init Hsafe stk buffer n Hi with ⟨sr, Hi'⟩
    cases sr with
    | Fail_sr_full _ _ => intro _; trivial
    | Accept_sr sem bn => exact id
    | Progress_sr stk' bn =>
      rintro ⟨word', hbuf, hw'⟩
      have := ih stk' word' bn (Hi' _ _ rfl) hw'
      revert this
      cases (parse_fix init Hsafe stk' bn n (Hi' _ _ rfl)).1 with
      | Fail_sr_full _ _ => intro _; trivial
      | Accept_sr sem bn' =>
        rintro ⟨word'', pt, h1, h2⟩
        exact ⟨word'', pt, hbuf.trans h1, h2⟩
      | Progress_sr stk'' bn' =>
        rintro ⟨word'', h1, h2⟩
        exact ⟨word'', hbuf.trans h1, h2⟩

/-- The interpreter is correct: if it returns a semantic value, then the input
word has this semantic value. -/
theorem parse_correct (init : initstate) (Hsafe : safe) (buffer : Buffer) (log_n_steps : Nat) :
    match parse init Hsafe buffer log_n_steps with
    | .Parsed_pr sem buffer_new =>
      ∃ word_new, ∃ pt : parse_tree (.NT (start_nt init)) word_new,
        buffer = app_buf word_new buffer_new ∧ pt_sem pt = sem
    | _ => True := by
  have := parse_fix_invariant init Hsafe log_n_steps [] [] buffer (stack_invariant_nil init)
    .nil
  unfold parse
  revert this
  cases (parse_fix init Hsafe [] buffer log_n_steps (stack_invariant_nil init)).1 with
  | Fail_sr_full _ _ => intro _; trivial
  | Accept_sr sem bn => exact id
  | Progress_sr _ _ => intro _; trivial

end Correct

end MenhirLib
end CC
