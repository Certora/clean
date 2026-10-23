/-
  First part of the port of `MenhirLib/Interpreter_complete.v`: dotted parse
  trees.

  Completeness is proved by following the traversal of the parse tree which
  is performed by the parser.  Each step of parsing corresponds to one step
  of traversal.  The state of the traversal is a "dotted" parse tree: a
  regular parse tree (the part under the dot) and a parse tree zipper (the
  part above the dot, represented upside down).

  This file defines zippers and dotted parse trees, the next dotted parse
  tree after one action (`next_ptd`), and proves that `next_ptd` preserves
  the semantic value (`sem_next_ptd`), the input buffer
  (`ptd_buffer_build_from_ptl`) and decreases the cost (`next_ptd_cost`).
  `Interpreter_complete.lean` relates dotted parse trees to the stack of the
  parser.

  Rocq builds the next dotted parse tree with `match` expressions that
  generalise the indices by hand; here the auxiliary function
  `next_ptd.next_of_ptz` takes general indices, and the choice between
  reducing and descending into a production tests `prod_rhs_rev prod = []`.
-/
import CCLib.MenhirLib.Interpreter

namespace CC
namespace MenhirLib

section Zipper
variable [Alphs] [GrammarT] [AutInit] [AutomatonT]
variable (init : initstate) (full_word : List token)

mutual
/-- A parse tree with a hole of symbol `hole_symb` recognising `hole_word`
(represented upside down). -/
inductive pt_zipper : Symbol → List token → Type where
  | Top_ptz : pt_zipper (.NT (start_nt init)) full_word
  | Cons_ptl_ptz {head_symbolsq : List Symbol} {wordq : List token} :
      parse_tree_list head_symbolsq wordq →
      {head_symbolt : Symbol} → {wordt : List token} →
      ptl_zipper (head_symbolt :: head_symbolsq) (wordq ++ wordt) →
      pt_zipper head_symbolt wordt

/-- A parse tree with a hole for a list of parse trees. -/
inductive ptl_zipper : List Symbol → List token → Type where
  | Non_terminal_pt_ptlz {p : production} {word : List token} :
      pt_zipper (.NT (prod_lhs p)) word → ptl_zipper (prod_rhs_rev p) word
  | Cons_ptl_ptlz {head_symbolsq : List Symbol} {wordq : List token}
      {head_symbolt : Symbol} {wordt : List token} :
      parse_tree head_symbolt wordt →
      ptl_zipper (head_symbolt :: head_symbolsq) (wordq ++ wordt) →
      ptl_zipper head_symbolsq wordq
end

/-- A dotted parse tree: a parse tree zipper and a parse tree, in two
flavours depending on the next action to be executed. -/
inductive pt_dot where
  | Reduce_ptd {prod : production} {word : List token} :
      parse_tree_list (prod_rhs_rev prod) word →
      pt_zipper init full_word (.NT (prod_lhs prod)) word → pt_dot
  | Shift_ptd (tok : token) {symbolsq : List Symbol} {wordq : List token} :
      parse_tree_list symbolsq wordq →
      ptl_zipper init full_word (.T (token_term tok) :: symbolsq) (wordq ++ [tok]) → pt_dot

variable {init} {full_word}

/-! ### Semantic values -/

mutual
def ptlz_sem : {hole_symbs : List Symbol} → {hole_word : List token} →
    ptl_zipper init full_word hole_symbs hole_word →
    (∀ A : Type, arrows_right A (hole_symbs.map symbol_semantic_type) → A) →
    symbol_semantic_type (.NT (start_nt init))
  | _, _, .Non_terminal_pt_ptlz (p := prod) ptz, k => ptz_sem ptz (k _ (prod_action prod))
  | _, _, .Cons_ptl_ptlz pt ptlz, k => ptlz_sem ptlz (fun _ f => k _ (f (pt_sem pt)))

def ptz_sem : {hole_symb : Symbol} → {hole_word : List token} →
    pt_zipper init full_word hole_symb hole_word →
    symbol_semantic_type hole_symb → symbol_semantic_type (.NT (start_nt init))
  | _, _, .Top_ptz, sem => sem
  | _, _, .Cons_ptl_ptz ptl ptlz, sem => ptlz_sem ptlz (fun _ f => ptl_sem ptl (f sem))
end

/-- The semantic value of the full parse tree represented by a dotted parse
tree. -/
def ptd_sem : pt_dot init full_word → symbol_semantic_type (.NT (start_nt init))
  | .Reduce_ptd (prod := prod) ptl ptz => ptz_sem ptz (ptl_sem ptl (prod_action prod))
  | .Shift_ptd tok ptl ptlz => ptlz_sem ptlz (fun _ f => ptl_sem ptl (f (token_sem tok)))

/-! ### Buffers -/

variable (buffer_end : Buffer)

mutual
/-- The buffer left to be read by the parser at the hole. -/
def ptlz_buffer : {hole_symbs : List Symbol} → {hole_word : List token} →
    ptl_zipper init full_word hole_symbs hole_word → Buffer
  | _, _, .Non_terminal_pt_ptlz ptz => ptz_buffer ptz
  | _, _, .Cons_ptl_ptlz (wordt := wordt) _ ptlz' => app_buf wordt (ptlz_buffer ptlz')

def ptz_buffer : {hole_symb : Symbol} → {hole_word : List token} →
    pt_zipper init full_word hole_symb hole_word → Buffer
  | _, _, .Top_ptz => buffer_end
  | _, _, .Cons_ptl_ptz _ ptlz => ptlz_buffer ptlz
end

def ptd_buffer : pt_dot init full_word → Buffer
  | .Reduce_ptd _ ptz => ptz_buffer buffer_end ptz
  | .Shift_ptd tok _ ptlz => Buf_cons tok (ptlz_buffer buffer_end ptlz)

/-! ### Next dotted parse tree -/

mutual
/-- Move the dot down in front of the next action to be performed, starting
from a parse tree. -/
def build_pt_dot_from_pt : {symb : Symbol} → {word : List token} →
    parse_tree symb word → pt_zipper init full_word symb word → pt_dot init full_word
  | _, _, .Terminal_pt tok, .Cons_ptl_ptz ptl ptlz => .Shift_ptd tok ptl ptlz
  | _, _, .Non_terminal_pt prod ptl, ptz =>
    if h : prod_rhs_rev prod = [] then .Reduce_ptd ptl ptz
    else build_pt_dot_from_pt_rec ptl h (.Non_terminal_pt_ptlz ptz)

/-- The same, from a non-empty list of parse trees. -/
def build_pt_dot_from_pt_rec : {symbs : List Symbol} → {word : List token} →
    parse_tree_list symbs word → symbs ≠ [] → ptl_zipper init full_word symbs word →
    pt_dot init full_word
  | _, _, .Nil_ptl, h, _ => absurd rfl h
  | _, _, .Cons_ptl .Nil_ptl pt, _, ptlz => build_pt_dot_from_pt pt (.Cons_ptl_ptz .Nil_ptl ptlz)
  | _, _, .Cons_ptl (.Cons_ptl ptl'' pt'') pt, _, ptlz =>
    build_pt_dot_from_pt_rec (.Cons_ptl ptl'' pt'') (List.cons_ne_nil _ _) (.Cons_ptl_ptlz pt ptlz)
end

def build_pt_dot_from_ptl : {symbs : List Symbol} → {word : List token} →
    parse_tree_list symbs word → ptl_zipper init full_word symbs word → pt_dot init full_word
  | _, _, ptl, .Non_terminal_pt_ptlz ptz => .Reduce_ptd ptl ptz
  | _, _, ptl, .Cons_ptl_ptlz pt ptlz => build_pt_dot_from_pt pt (.Cons_ptl_ptz ptl ptlz)

/-- After a reduction completing the parse tree `pt` placed at the hole of
`ptz`. -/
def next_of_ptz : {symb : Symbol} → {word : List token} →
    pt_zipper init full_word symb word → parse_tree symb word → Option (pt_dot init full_word)
  | _, _, .Top_ptz, _ => none
  | _, _, .Cons_ptl_ptz ptl' ptlz, pt => some (build_pt_dot_from_ptl (.Cons_ptl ptl' pt) ptlz)

/-- The dotted parse tree after one action. -/
def next_ptd : pt_dot init full_word → Option (pt_dot init full_word)
  | .Shift_ptd tok ptl ptlz => some (build_pt_dot_from_ptl (.Cons_ptl ptl (.Terminal_pt tok)) ptlz)
  | .Reduce_ptd (prod := prod) ptl ptz => next_of_ptz ptz (.Non_terminal_pt prod ptl)

/-- `2 ^ log_n_steps` iterations of `next_ptd`. -/
def next_ptd_iter (ptd : pt_dot init full_word) : Nat → Option (pt_dot init full_word)
  | 0 => next_ptd ptd
  | n + 1 =>
    match next_ptd_iter ptd n with
    | none => none
    | some ptd => next_ptd_iter ptd n

/-! ### Cost: the number of actions left before the end of the parsing -/

mutual
def ptlz_cost : {hole_symbs : List Symbol} → {hole_word : List token} →
    ptl_zipper init full_word hole_symbs hole_word → Nat
  | _, _, .Non_terminal_pt_ptlz ptz => ptz_cost ptz
  | _, _, .Cons_ptl_ptlz pt ptlz' => pt_size pt + ptlz_cost ptlz'

def ptz_cost : {hole_symb : Symbol} → {hole_word : List token} →
    pt_zipper init full_word hole_symb hole_word → Nat
  | _, _, .Top_ptz => 0
  | _, _, .Cons_ptl_ptz _ ptlz' => 1 + ptlz_cost ptlz'
end

def ptd_cost : pt_dot init full_word → Nat
  | .Reduce_ptd _ ptz => ptz_cost ptz
  | .Shift_ptd _ _ ptlz => 1 + ptlz_cost ptlz

/-! ### `next_ptd` preserves the semantic value -/

omit [AutInit] [AutomatonT] in
theorem ptl_nil_word {word : List token} : ∀ {symbs : List Symbol},
    parse_tree_list symbs word → symbs = [] → word = []
  | _, .Nil_ptl, _ => rfl
  | _, .Cons_ptl _ _, h => absurd h (List.cons_ne_nil _ _)

omit [AutInit] [AutomatonT] in
theorem app_buf_of_nil {word : List token} : ∀ {symbs : List Symbol},
    parse_tree_list symbs word → symbs = [] → ∀ b : Buffer, app_buf word b = b
  | _, .Nil_ptl, _, _ => rfl
  | _, .Cons_ptl _ _, h, _ => absurd h (List.cons_ne_nil _ _)

omit [AutInit] [AutomatonT] in
theorem ptl_size_nil {word : List token} : ∀ {symbs : List Symbol}
    (ptl : parse_tree_list symbs word), symbs = [] → ptl_size ptl = 0
  | _, .Nil_ptl, _ => by simp
  | _, .Cons_ptl _ _, h => absurd h (List.cons_ne_nil _ _)

mutual
theorem sem_build_from_pt : {symb : Symbol} → {word : List token} →
    (pt : parse_tree symb word) → (ptz : pt_zipper init full_word symb word) →
    ptz_sem ptz (pt_sem pt) = ptd_sem (build_pt_dot_from_pt pt ptz)
  | _, _, .Terminal_pt tok, .Cons_ptl_ptz ptl ptlz => by
    simp [build_pt_dot_from_pt, ptd_sem, ptz_sem]
  | _, _, .Non_terminal_pt prod ptl, ptz => by
    by_cases h : prod_rhs_rev prod = []
    · simp [build_pt_dot_from_pt, h, ptd_sem]
    · rw [build_pt_dot_from_pt, dif_neg h, ← sem_build_from_pt_rec ptl _ h]
      simp [ptlz_sem]

theorem sem_build_from_pt_rec : {symbs : List Symbol} → {word : List token} →
    (ptl : parse_tree_list symbs word) → (ptlz : ptl_zipper init full_word symbs word) →
    (h : symbs ≠ []) →
    ptlz_sem ptlz (fun _ f => ptl_sem ptl f) = ptd_sem (build_pt_dot_from_pt_rec ptl h ptlz)
  | _, _, .Nil_ptl, _, h => absurd rfl h
  | _, _, .Cons_ptl .Nil_ptl pt, ptlz, _ => by
    rw [build_pt_dot_from_pt_rec, ← sem_build_from_pt, ptz_sem]
    congr 1
    funext A f
    rw [ptl_sem_Cons_ptl_Nil, ptl_sem_Nil_ptl]
  | _, _, .Cons_ptl (.Cons_ptl ptl'' pt'') pt, ptlz, _ => by
    rw [build_pt_dot_from_pt_rec, ← sem_build_from_pt_rec]
    simp [ptlz_sem]
end

theorem sem_build_from_ptl : {symbs : List Symbol} → {word : List token} →
    (ptl : parse_tree_list symbs word) → (ptlz : ptl_zipper init full_word symbs word) →
    ptlz_sem ptlz (fun _ f => ptl_sem ptl f) = ptd_sem (build_pt_dot_from_ptl ptl ptlz)
  | _, _, ptl, .Non_terminal_pt_ptlz ptz => by simp [build_pt_dot_from_ptl, ptd_sem, ptlz_sem]
  | _, _, ptl, .Cons_ptl_ptlz pt ptlz => by
    rw [build_pt_dot_from_ptl, ← sem_build_from_pt]
    simp [ptz_sem, ptlz_sem]

theorem sem_next_of_ptz : {symb : Symbol} → {word : List token} →
    (ptz : pt_zipper init full_word symb word) → (pt : parse_tree symb word) →
    ∀ ptd', next_of_ptz ptz pt = some ptd' → ptz_sem ptz (pt_sem pt) = ptd_sem ptd'
  | _, _, .Top_ptz, _, _, h => by simp [next_of_ptz] at h
  | _, _, .Cons_ptl_ptz ptl' ptlz, pt, ptd', h => by
    simp only [next_of_ptz, Option.some.injEq] at h
    subst h
    rw [← sem_build_from_ptl]
    simp [ptz_sem]

theorem sem_next_ptd (ptd : pt_dot init full_word) :
    ∀ ptd', next_ptd ptd = some ptd' → ptd_sem ptd = ptd_sem ptd' := by
  intro ptd' h
  match ptd with
  | .Reduce_ptd (prod := prod) ptl ptz =>
    have := sem_next_of_ptz ptz (.Non_terminal_pt prod ptl) ptd' h
    simpa [ptd_sem] using this
  | .Shift_ptd tok ptl ptlz =>
    simp only [next_ptd, Option.some.injEq] at h
    subst h
    rw [← sem_build_from_ptl]
    simp [ptd_sem]

theorem sem_next_ptd_iter (ptd : pt_dot init full_word) (log_n_steps : Nat) :
    ∀ ptd', next_ptd_iter ptd log_n_steps = some ptd' → ptd_sem ptd = ptd_sem ptd' := by
  induction log_n_steps generalizing ptd with
  | zero => exact sem_next_ptd ptd
  | succ n ih =>
    intro ptd' h
    simp only [next_ptd_iter] at h
    revert h
    cases h1 : next_ptd_iter ptd n with
    | none => simp
    | some ptd1 =>
      intro h
      exact (ih ptd ptd1 h1).trans (ih ptd1 ptd' h)

/-! ### `next_ptd` preserves the buffer -/

mutual
theorem ptd_buffer_build_from_pt : {symb : Symbol} → {word : List token} →
    (pt : parse_tree symb word) → (ptz : pt_zipper init full_word symb word) →
    app_buf word (ptz_buffer buffer_end ptz) = ptd_buffer buffer_end (build_pt_dot_from_pt pt ptz)
  | _, _, .Terminal_pt tok, .Cons_ptl_ptz ptl ptlz => by
    simp [build_pt_dot_from_pt, ptd_buffer, ptz_buffer, app_buf]
  | _, _, .Non_terminal_pt prod ptl, ptz => by
    by_cases h : prod_rhs_rev prod = []
    · simp only [build_pt_dot_from_pt, h, dite_true, ptd_buffer]
      exact app_buf_of_nil ptl h _
    · rw [build_pt_dot_from_pt, dif_neg h, ← ptd_buffer_build_from_pt_rec ptl _ h]
      simp [ptlz_buffer]

theorem ptd_buffer_build_from_pt_rec : {symbs : List Symbol} → {word : List token} →
    (ptl : parse_tree_list symbs word) → (ptlz : ptl_zipper init full_word symbs word) →
    (h : symbs ≠ []) →
    app_buf word (ptlz_buffer buffer_end ptlz) =
      ptd_buffer buffer_end (build_pt_dot_from_pt_rec ptl h ptlz)
  | _, _, .Nil_ptl, _, h => absurd rfl h
  | _, _, .Cons_ptl .Nil_ptl pt, ptlz, _ => by
    rw [build_pt_dot_from_pt_rec, ← ptd_buffer_build_from_pt]
    simp [ptz_buffer]
  | _, _, .Cons_ptl (.Cons_ptl ptl'' pt'') pt, ptlz, _ => by
    rw [build_pt_dot_from_pt_rec, ← ptd_buffer_build_from_pt_rec]
    simp [ptlz_buffer, app_buf_assoc]
end

theorem ptd_buffer_build_from_ptl : {symbs : List Symbol} → {word : List token} →
    (ptl : parse_tree_list symbs word) → (ptlz : ptl_zipper init full_word symbs word) →
    ptlz_buffer buffer_end ptlz = ptd_buffer buffer_end (build_pt_dot_from_ptl ptl ptlz)
  | _, _, ptl, .Non_terminal_pt_ptlz ptz => by
    simp [build_pt_dot_from_ptl, ptd_buffer, ptlz_buffer]
  | _, _, ptl, .Cons_ptl_ptlz pt ptlz => by
    rw [build_pt_dot_from_ptl, ← ptd_buffer_build_from_pt]
    simp [ptz_buffer, ptlz_buffer]

/-! ### `next_ptd` decreases the cost -/

mutual
theorem ptd_cost_build_from_pt : {symb : Symbol} → {word : List token} →
    (pt : parse_tree symb word) → (ptz : pt_zipper init full_word symb word) →
    pt_size pt + ptz_cost ptz = ptd_cost (build_pt_dot_from_pt pt ptz) + 1
  | _, _, .Terminal_pt tok, .Cons_ptl_ptz ptl ptlz => by
    simp [build_pt_dot_from_pt, ptd_cost, ptz_cost]; omega
  | _, _, .Non_terminal_pt prod ptl, ptz => by
    by_cases h : prod_rhs_rev prod = []
    · simp only [build_pt_dot_from_pt, h, dite_true, ptd_cost, pt_size_Non_terminal_pt]
      rw [ptl_size_nil ptl h]; omega
    · rw [build_pt_dot_from_pt, dif_neg h, ← ptd_cost_build_from_pt_rec ptl _ h]
      simp [ptlz_cost]; omega

theorem ptd_cost_build_from_pt_rec : {symbs : List Symbol} → {word : List token} →
    (ptl : parse_tree_list symbs word) → (ptlz : ptl_zipper init full_word symbs word) →
    (h : symbs ≠ []) →
    ptl_size ptl + ptlz_cost ptlz = ptd_cost (build_pt_dot_from_pt_rec ptl h ptlz)
  | _, _, .Nil_ptl, _, h => absurd rfl h
  | _, _, .Cons_ptl .Nil_ptl pt, ptlz, _ => by
    rw [build_pt_dot_from_pt_rec]
    have := ptd_cost_build_from_pt pt (.Cons_ptl_ptz .Nil_ptl ptlz)
    rw [ptl_size_Cons_ptl_Nil]
    simp only [ptz_cost] at this; omega
  | _, _, .Cons_ptl (.Cons_ptl ptl'' pt'') pt, ptlz, _ => by
    rw [build_pt_dot_from_pt_rec, ← ptd_cost_build_from_pt_rec]
    simp [ptlz_cost]; omega
end

theorem ptd_cost_build_from_ptl : {symbs : List Symbol} → {word : List token} →
    (ptl : parse_tree_list symbs word) → (ptlz : ptl_zipper init full_word symbs word) →
    ptlz_cost ptlz = ptd_cost (build_pt_dot_from_ptl ptl ptlz)
  | _, _, ptl, .Non_terminal_pt_ptlz ptz => by
    simp [build_pt_dot_from_ptl, ptd_cost, ptlz_cost]
  | _, _, ptl, .Cons_ptl_ptlz pt ptlz => by
    rw [build_pt_dot_from_ptl]
    have := ptd_cost_build_from_pt pt (.Cons_ptl_ptz ptl ptlz)
    simp [ptz_cost] at this; simp [ptlz_cost]; omega

theorem next_of_ptz_cost : {symb : Symbol} → {word : List token} →
    (ptz : pt_zipper init full_word symb word) → (pt : parse_tree symb word) →
    match next_of_ptz ptz pt with
    | none => ptz_cost ptz = 0
    | some ptd' => ptz_cost ptz = ptd_cost ptd' + 1
  | _, _, .Top_ptz, _ => by simp [next_of_ptz, ptz_cost]
  | _, _, .Cons_ptl_ptz ptl' ptlz, pt => by
    simp only [next_of_ptz, ptz_cost]
    rw [← ptd_cost_build_from_ptl]; omega

theorem next_ptd_cost (ptd : pt_dot init full_word) :
    match next_ptd ptd with
    | none => ptd_cost ptd = 0
    | some ptd' => ptd_cost ptd = ptd_cost ptd' + 1 := by
  match ptd with
  | .Reduce_ptd (prod := prod) ptl ptz =>
    have := next_of_ptz_cost ptz (.Non_terminal_pt prod ptl)
    simpa [next_ptd, ptd_cost] using this
  | .Shift_ptd tok ptl ptlz =>
    have := ptd_cost_build_from_ptl (.Cons_ptl ptl (.Terminal_pt tok)) ptlz
    simp only [next_ptd]
    rw [← this]
    show 1 + ptlz_cost ptlz = ptlz_cost ptlz + 1
    omega

theorem next_ptd_iter_cost (ptd : pt_dot init full_word) (log_n_steps : Nat) :
    match next_ptd_iter ptd log_n_steps with
    | none => ptd_cost ptd < 2 ^ log_n_steps
    | some ptd' => ptd_cost ptd = 2 ^ log_n_steps + ptd_cost ptd' := by
  induction log_n_steps generalizing ptd with
  | zero =>
    have := next_ptd_cost ptd
    simp only [next_ptd_iter]
    revert this
    cases next_ptd ptd with
    | none => intro h; simp [h]
    | some ptd' => intro h; simp [h]; omega
  | succ n ih =>
    have ih1 := ih ptd
    simp only [next_ptd_iter]
    revert ih1
    cases next_ptd_iter ptd n with
    | none => intro h; simp only; rw [Nat.pow_succ]; omega
    | some ptd1 =>
      intro h1
      have ih2 := ih ptd1
      simp only
      revert ih2
      cases next_ptd_iter ptd1 n with
      | none => intro h2; simp only at h1 h2 ⊢; rw [Nat.pow_succ]; omega
      | some ptd2 => intro h2; simp only at h1 h2 ⊢; rw [Nat.pow_succ]; omega

end Zipper

end MenhirLib
end CC
