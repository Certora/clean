/-
  Checks of the verified C parser `CCLib/cparser/Parser.lean` on small token
  streams (the lexer and the pre-parser that classify identifiers into
  `VAR_NAME`/`TYPEDEF_NAME`/`OTHER_NAME` are OCaml code in CompCert and are not
  ported, so the token streams are written by hand).
-/
import CCLib.cparser.Parser

namespace CC.ParserCheck

open CC.Parser CC.MenhirLib CC.Cabs

def l : Loc := { lineno := 1, filename := "t.c", byteno := 0, ident := 0 }

/-- The input buffer made of a list of tokens, followed by `EOF` forever. -/
def bufOf (toks : List Token) : Nat → Token := fun n => toks.getD n (.EOF ())

/-- Number of definitions parsed, or `none` if the parser did not accept. -/
def parsedCount (toks : List Token) : Option Nat :=
  match translation_unit_file 20 (bufOf toks) with
  | .Parsed_pr defs _ => some defs.length
  | _ => none

/-- `int main() { return 0; }` -/
def prog1 : List Token :=
  [.INT l, .VAR_NAME ("main", l), .LPAREN l, .RPAREN l, .LBRACE l,
   .RETURN l, .CONSTANT (.CONST_INT "0", l), .SEMICOLON l, .RBRACE l, .EOF ()]

/-- `int x = 1 + 2 * 3; static int *p;` -/
def prog2 : List Token :=
  [.INT l, .VAR_NAME ("x", l), .EQ l, .CONSTANT (.CONST_INT "1", l), .PLUS l,
   .CONSTANT (.CONST_INT "2", l), .STAR l, .CONSTANT (.CONST_INT "3", l), .SEMICOLON l,
   .STATIC l, .INT l, .STAR l, .VAR_NAME ("p", l), .SEMICOLON l, .EOF ()]

/-- `void f(int a) { if (a) if (a) a = 1; else a = 2; }` (dangling `else`). -/
def prog3 : List Token :=
  [.VOID l, .VAR_NAME ("f", l), .LPAREN l, .INT l, .VAR_NAME ("a", l), .RPAREN l, .LBRACE l,
   .IF_ l, .LPAREN l, .VAR_NAME ("a", l), .RPAREN l,
   .IF_ l, .LPAREN l, .VAR_NAME ("a", l), .RPAREN l,
   .VAR_NAME ("a", l), .EQ l, .CONSTANT (.CONST_INT "1", l), .SEMICOLON l,
   .ELSE l, .VAR_NAME ("a", l), .EQ l, .CONSTANT (.CONST_INT "2", l), .SEMICOLON l,
   .RBRACE l, .EOF ()]

/-- `int x = ;` is rejected. -/
def bad1 : List Token :=
  [.INT l, .VAR_NAME ("x", l), .EQ l, .SEMICOLON l, .EOF ()]

/-- The `else` of `prog3` is attached to the inner `if`. -/
def danglingElseInner (toks : List Token) : Bool :=
  match translation_unit_file 20 (bufOf toks) with
  | .Parsed_pr [.FUNDEF _ _ _ (.BLOCK [.If _ (.If _ _ (some _) _) none _] _) _] _ => true
  | _ => false

example : parsedCount prog1 = some 1 := by native_decide
example : parsedCount prog2 = some 2 := by native_decide
example : parsedCount prog3 = some 1 := by native_decide
example : danglingElseInner prog3 = true := by native_decide
example : parsedCount bad1 = none := by native_decide
example : parsedCount [.EOF ()] = some 0 := by native_decide

/-! ### A long input

`n` declarations `int x;`, read from an array.  Compiled code runs the
offset-based interpreter of `MenhirLib/InterpreterFast.lean` (substituted for
`parse` by `@[csimp]`), so reading a token costs `O(1)`; with the buffers of
`Interpreter.lean`, the `k`-th token would be read through `k` closures. -/

/-- The tokens of `n` declarations `int x;`, followed by `EOF`. -/
def manyDecls (n : Nat) : Array Token := Id.run do
  let mut a := #[]
  for _ in [0:n] do
    a := a.push (.INT l) |>.push (.VAR_NAME ("x", l)) |>.push (.SEMICOLON l)
  return a.push (.EOF ())

/-- Number of definitions parsed from an array of tokens. -/
def parsedCountArr (toks : Array Token) : Option Nat :=
  match translation_unit_file 24 (fun n => toks.getD n (.EOF ())) with
  | .Parsed_pr defs _ => some defs.length
  | _ => none

example : parsedCountArr (manyDecls 20000) = some 20000 := by native_decide

end CC.ParserCheck
