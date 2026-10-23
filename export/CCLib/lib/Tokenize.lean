/-
  Port of `lib/Tokenize.mll`: split a string into a list of tokens (used to
  parse `#pragma` directives, see `cfrontend/CPragmas.lean`).

  The `ocamllex` rules are a hand-written scanner over the list of
  characters:
  * blanks (space, tab, newline, carriage return) separate tokens;
  * `"..."` is one token (the escapes `\t`, `\n`, `\r`, `\\`, `\"` are
    decoded), and so is `'...'` (no escapes); an unterminated quote ends
    at the end of the string;
  * an identifier starts with a letter, digit, `$` or `_` and continues
    with these characters and `-`, `.`;
  * any other character is a token of its own.
-/

namespace CC
namespace Tokenize

/-- `identstart` -/
def identstart (c : Char) : Bool := c.isAlphanum || c == '$' || c == '_'

/-- `identcont` -/
def identcont (c : Char) : Bool := identstart c || c == '-' || c == '.'

/-- `tok_dquote`: the contents of a double-quoted string, up to the closing
    quote (or the end of input); returns the token and the rest. -/
def tok_dquote (buf : String) : List Char → String × List Char
  | [] => (buf, [])
  | '"' :: rest => (buf, rest)
  | '\\' :: 't' :: rest => tok_dquote (buf.push '\t') rest
  | '\\' :: 'n' :: rest => tok_dquote (buf.push '\n') rest
  | '\\' :: 'r' :: rest => tok_dquote (buf.push '\r') rest
  | '\\' :: '\\' :: rest => tok_dquote (buf.push '\\') rest
  | '\\' :: '"' :: rest => tok_dquote (buf.push '"') rest
  | c :: rest => tok_dquote (buf.push c) rest

/-- `tok_squote`: the contents of a single-quoted string. -/
def tok_squote (buf : String) : List Char → String × List Char
  | [] => (buf, [])
  | '\'' :: rest => (buf, rest)
  | c :: rest => tok_squote (buf.push c) rest

theorem tok_dquote_length (buf : String) (cs : List Char) :
    (tok_dquote buf cs).2.length ≤ cs.length := by
  induction buf, cs using tok_dquote.induct <;> simp_all [tok_dquote] <;> omega

theorem tok_squote_length (buf : String) (cs : List Char) :
    (tok_squote buf cs).2.length ≤ cs.length := by
  induction buf, cs using tok_squote.induct <;> simp_all [tok_squote] <;> omega

/-- `tokenize` -/
def tokenize (acc : List String) : List Char → List String
  | [] => acc.reverse
  | c :: rest =>
    if c == ' ' || c == '\t' || c == '\n' || c == '\r' then tokenize acc rest
    else if c == '"' then
      let r := tok_dquote "" rest
      have := tok_dquote_length "" rest
      tokenize (r.1 :: acc) r.2
    else if c == '\'' then
      let r := tok_squote "" rest
      have := tok_squote_length "" rest
      tokenize (r.1 :: acc) r.2
    else if identstart c then
      let s := rest.takeWhile identcont
      have : (rest.dropWhile identcont).length ≤ rest.length := by
        induction rest with
        | nil => simp
        | cons x xs ih => simp only [List.dropWhile]; split <;> simp <;> omega
      tokenize (String.ofList (c :: s) :: acc) (rest.dropWhile identcont)
    else tokenize (String.singleton c :: acc) rest
termination_by cs => cs.length

/-- `Tokenize.string` -/
def string (s : String) : List String := tokenize [] s.toList

end Tokenize
end CC
