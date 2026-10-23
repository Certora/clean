/-
  Port of `MenhirLib/Grammar.v`: grammars and their semantics (parse trees).

  Rocq's module types `Alphs` and `T` become the classes `Alphs` and
  `GrammarT`; the functors `Symbol` and `Defs` become definitions
  parameterised by these classes.
-/
import CCLib.MenhirLib.Alphabet

namespace CC
namespace MenhirLib

/-- The terminal and non-terminal alphabets of the grammar. -/
class Alphs where
  terminal : Type
  nonterminal : Type
  [terminalAlph : Alphabet terminal]
  [nonterminalAlph : Alphabet nonterminal]

export Alphs (terminal nonterminal)

@[reducible] instance Alphs.instTerminalAlph [A : Alphs] : Alphabet A.terminal := A.terminalAlph
@[reducible] instance Alphs.instNonterminalAlph [A : Alphs] : Alphabet A.nonterminal :=
  A.nonterminalAlph

/-- The alphabet of symbols, given the alphabets of terminals and of
non-terminals. -/
inductive Symbol [Alphs] where
  | T : terminal → Symbol
  | NT : nonterminal → Symbol

namespace Symbol
variable [Alphs]

def inj : Symbol → Nat
  | .T t => 2 * Alphabet.inj t
  | .NT n => 2 * Alphabet.inj n + 1

theorem inj_inj (x y : Symbol) (h : x.inj = y.inj) : x = y := by
  cases x with
  | T a => cases y with
    | T b => rw [Alphabet.inj_inj a b (by simp only [inj] at h; omega)]
    | NT b => simp only [inj] at h; omega
  | NT a => cases y with
    | T b => simp only [inj] at h; omega
    | NT b => rw [Alphabet.inj_inj a b (by simp only [inj] at h; omega)]

instance alphabet : Alphabet Symbol where
  inj := Symbol.inj
  inj_inj := Symbol.inj_inj
  all_list := (all_list : List terminal).map Symbol.T ++ (all_list : List nonterminal).map Symbol.NT
  all_list_forall x := by
    cases x with
    | T t => exact List.mem_append_left _ (List.mem_map_of_mem (all_list_forall t))
    | NT n => exact List.mem_append_right _ (List.mem_map_of_mem (all_list_forall n))

instance : DecidableEq Symbol := Alphabet.decEq

end Symbol

/-- A curryfied function with multiple parameters. -/
def arrows_right : Type → List Type → Type
  | A, [] => A
  | A, B :: l => B → arrows_right A l

/-- A grammar (Rocq's module type `Grammar.T`). -/
class GrammarT [Alphs] where
  /-- The type of the semantic values of each symbol. -/
  symbol_semantic_type : Symbol → Type
  /-- The type of productions identifiers. -/
  production : Type
  [productionAlph : Alphabet production]
  /-- Left hand side of a production. -/
  prod_lhs : production → nonterminal
  /-- The right hand side of a production, in reverse order. -/
  prod_rhs_rev : production → List Symbol
  /-- The semantic action of a production, taking its arguments in reverse
  order. -/
  prod_action : ∀ p : production,
    arrows_right (symbol_semantic_type (.NT (prod_lhs p)))
      ((prod_rhs_rev p).map symbol_semantic_type)
  /-- Tokens: a terminal with a semantic value. -/
  token : Type
  token_term : token → terminal
  token_sem : ∀ tok : token, symbol_semantic_type (.T (token_term tok))

export GrammarT (symbol_semantic_type production prod_lhs prod_rhs_rev prod_action token
  token_term token_sem)

@[reducible] instance GrammarT.instProductionAlph [Alphs] [G : GrammarT] :
    Alphabet G.production := G.productionAlph

section Defs
variable [Alphs] [GrammarT]

mutual
/-- Parse trees for a single head symbol. -/
inductive parse_tree : Symbol → List token → Type where
  /-- Parse tree for a terminal symbol. -/
  | Terminal_pt (tok : token) : parse_tree (.T (token_term tok)) [tok]
  /-- Parse tree for a non-terminal symbol. -/
  | Non_terminal_pt (prod : production) {word : List token} :
      parse_tree_list (prod_rhs_rev prod) word → parse_tree (.NT (prod_lhs prod)) word

/-- Parse trees for a list of head symbols (in reverse order). -/
inductive parse_tree_list : List Symbol → List token → Type where
  | Nil_ptl : parse_tree_list [] []
  | Cons_ptl {head_symbolsq : List Symbol} {wordq : List token} :
      parse_tree_list head_symbolsq wordq →
      {head_symbolt : Symbol} → {wordt : List token} →
      parse_tree head_symbolt wordt →
      parse_tree_list (head_symbolt :: head_symbolsq) (wordq ++ wordt)
end

mutual
/-- The semantic value of a parse tree. -/
def pt_sem : {head_symbol : Symbol} → {word : List token} →
    parse_tree head_symbol word → symbol_semantic_type head_symbol
  | _, _, .Terminal_pt tok => token_sem tok
  | _, _, .Non_terminal_pt prod ptl => ptl_sem ptl (prod_action prod)

/-- The semantic value of a list of parse trees, given to a semantic action. -/
def ptl_sem {A : Type} : {head_symbols : List Symbol} → {word : List token} →
    parse_tree_list head_symbols word →
    arrows_right A (head_symbols.map symbol_semantic_type) → A
  | _, _, .Nil_ptl, act => act
  | _, _, .Cons_ptl q t, act => ptl_sem q (act (pt_sem t))
end

mutual
/-- The size of a parse tree. -/
def pt_size : {head_symbol : Symbol} → {word : List token} → parse_tree head_symbol word → Nat
  | _, _, .Terminal_pt _ => 1
  | _, _, .Non_terminal_pt _ l => ptl_size l + 1

def ptl_size : {head_symbols : List Symbol} → {word : List token} →
    parse_tree_list head_symbols word → Nat
  | _, _, .Nil_ptl => 0
  | _, _, .Cons_ptl q t => pt_size t + ptl_size q
end

@[simp] theorem pt_sem_Terminal_pt (tok : token) : pt_sem (.Terminal_pt tok) = token_sem tok := by
  simp [pt_sem]

@[simp] theorem pt_sem_Non_terminal_pt (prod : production) {word : List token}
    (ptl : parse_tree_list (prod_rhs_rev prod) word) :
    pt_sem (.Non_terminal_pt prod ptl) = ptl_sem ptl (prod_action prod) := by
  simp [pt_sem]

@[simp] theorem ptl_sem_Nil_ptl {A : Type} (act : arrows_right A []) :
    ptl_sem (A := A) .Nil_ptl act = act := by
  simp [ptl_sem]

@[simp] theorem ptl_sem_Cons_ptl {A : Type} {hsq : List Symbol} {wq : List token}
    (q : parse_tree_list hsq wq) {hst : Symbol} {wt : List token} (t : parse_tree hst wt)
    (act : arrows_right A ((hst :: hsq).map symbol_semantic_type)) :
    ptl_sem (.Cons_ptl q t) act = ptl_sem q (act (pt_sem t)) := by
  simp [ptl_sem]

/-- `ptl_sem_Cons_ptl` for a single tree (`simp` does not use the general
lemma there, because the index `[] ++ wt` is reduced in the term). -/
@[simp] theorem ptl_sem_Cons_ptl_Nil {A : Type} {hst : Symbol} {wt : List token}
    (t : parse_tree hst wt) (act : arrows_right A ([hst].map symbol_semantic_type)) :
    ptl_sem (.Cons_ptl .Nil_ptl t) act = act (pt_sem t) := by
  rw [ptl_sem_Cons_ptl, ptl_sem_Nil_ptl]

@[simp] theorem pt_size_Terminal_pt (tok : token) : pt_size (.Terminal_pt tok) = 1 := by
  simp [pt_size]

@[simp] theorem pt_size_Non_terminal_pt (prod : production) {word : List token}
    (ptl : parse_tree_list (prod_rhs_rev prod) word) :
    pt_size (.Non_terminal_pt prod ptl) = ptl_size ptl + 1 := by
  simp [pt_size]

@[simp] theorem ptl_size_Nil_ptl : ptl_size (.Nil_ptl : parse_tree_list [] []) = 0 := by
  simp [ptl_size]

@[simp] theorem ptl_size_Cons_ptl {hsq : List Symbol} {wq : List token}
    (q : parse_tree_list hsq wq) {hst : Symbol} {wt : List token} (t : parse_tree hst wt) :
    ptl_size (.Cons_ptl q t) = pt_size t + ptl_size q := by
  simp [ptl_size]

@[simp] theorem ptl_size_Cons_ptl_Nil {hst : Symbol} {wt : List token} (t : parse_tree hst wt) :
    ptl_size (.Cons_ptl .Nil_ptl t) = pt_size t := by
  rw [ptl_size_Cons_ptl, ptl_size_Nil_ptl, Nat.add_zero]

end Defs

end MenhirLib
end CC
