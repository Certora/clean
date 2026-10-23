/-
  Port of `cparser/deLexer.ml`: converting a terminal symbol of the C
  grammar back to a concrete string that the lexer accepts.  This is used to
  turn an error sentence produced by Menhir (a space-separated list of
  terminal names) into C code.

  Differences from OCaml:
  * The terminals are those of the verified parser (`CC.Parser.Terminal`),
    so `delex` is a total function on them.  `deLexer.ml` matches on symbol
    names and raises `Not_found` for the three terminals it does not list:
    here `NORETURN` and `FLOAT16` are de-lexed to `_Noreturn` and
    `_Float16` (which `Lexer.lexicon` accepts), and `OTHER_NAME` (the Lean
    lexer's counterpart of the pre-parser's `PRE_NAME`) to the empty
    string, like `PRE_NAME`.
  * The symbol-name interface (`delexSymbol`, `delexSentence`) returns an
    `Option`/`Except` instead of raising, and `delexSentence` returns the
    text that the OCaml script prints (each symbol followed by a space)
    instead of printing it.
  `ParseCheck` (in `export/examples/`) checks that the lexer reads each
  `delex t` back as the terminal `t`.
-/
import CCLib.cparser.Parser

namespace CC
namespace DeLexer

open Parser

/-- `delex`: a concrete string that the lexer reads as the terminal `t`. -/
def delex : Terminal → String
  | .ALIGNAS => "_Alignas"
  | .ALIGNOF => "__alignof__"  -- the gcc-compatible form
  | .UNDERSCORE_BOOL => "_Bool"
  | .ASM => "__asm"
  | .ATTRIBUTE => "__attribute"
  | .BUILTIN_VA_ARG => "__builtin_va_arg"
  | .CONST => "const"
  | .INLINE => "inline"
  | .PACKED => "__packed__"
  | .RESTRICT => "restrict"
  | .SIGNED => "signed"
  | .VOLATILE => "volatile"
  | .AUTO => "auto"
  | .BREAK => "break"
  | .CASE => "case"
  | .CHAR => "char"
  | .CONTINUE => "continue"
  | .DEFAULT => "default"
  | .DO => "do"
  | .DOUBLE => "double"
  | .ELSE => "else"
  | .ENUM => "enum"
  | .EXTERN => "extern"
  | .FLOAT => "float"
  | .FLOAT16 => "_Float16"
  | .FOR => "for"
  | .GENERIC => "_Generic"
  | .GOTO => "goto"
  | .IF_ => "if"
  | .INT => "int"
  | .LONG => "long"
  | .NORETURN => "_Noreturn"
  | .REGISTER => "register"
  | .RETURN => "return"
  | .SHORT => "short"
  | .SIZEOF => "sizeof"
  | .STATIC => "static"
  | .STRUCT => "struct"
  | .SWITCH => "switch"
  | .TYPEDEF => "typedef"
  | .UNION => "union"
  | .UNSIGNED => "unsigned"
  | .VOID => "void"
  | .WHILE => "while"
  | .TYPEDEF_NAME => "t"  -- this should be a type name
  | .VAR_NAME => "x"  -- this should be a variable name
  | .OTHER_NAME => ""
  | .CONSTANT => "42"
  | .STRING_LITERAL => "\"\""
  | .ELLIPSIS => "..."
  | .ADD_ASSIGN => "+="
  | .SUB_ASSIGN => "-="
  | .MUL_ASSIGN => "*="
  | .DIV_ASSIGN => "/="
  | .MOD_ASSIGN => "%="
  | .OR_ASSIGN => "|="
  | .AND_ASSIGN => "&="
  | .XOR_ASSIGN => "^="
  | .LEFT_ASSIGN => "<<="
  | .RIGHT_ASSIGN => ">>="
  | .LEFT => "<<"
  | .RIGHT => ">>"
  | .EQEQ => "=="
  | .NEQ => "!="
  | .LEQ => "<="
  | .GEQ => ">="
  | .EQ => "="
  | .LT => "<"
  | .GT => ">"
  | .INC => "++"
  | .DEC => "--"
  | .PTR => "->"
  | .PLUS => "+"
  | .MINUS => "-"
  | .STAR => "*"
  | .SLASH => "/"
  | .PERCENT => "%"
  | .BANG => "!"
  | .ANDAND => "&&"
  | .BARBAR => "||"
  | .AND => "&"
  | .BAR => "|"
  | .HAT => "^"
  | .QUESTION => "?"
  | .COLON => ":"
  | .TILDE => "~"
  | .LBRACE => "{"
  | .RBRACE => "}"
  | .LBRACK => "["
  | .RBRACK => "]"
  | .LPAREN => "("
  | .RPAREN => ")"
  | .SEMICOLON => ";"
  | .COMMA => ","
  | .DOT => "."
  | .PRAGMA => "#pragma \n"
  | .BUILTIN_OFFSETOF => "__builtin_offsetof"
  | .STATIC_ASSERT => "_Static_assert"
  | .EOF => ""  -- this should be ok

/-- Menhir's name of a terminal (the constructor name; `IF_` is `IF`). -/
def symbolName (t : Terminal) : String :=
  match t with
  | .IF_ => "IF"
  | _ => ((reprStr t).splitOn ".").getLast!

/-- `delex` on a symbol name, as in `deLexer.ml` (`PRE_NAME` is the
    pre-parser's name for a not-yet-classified identifier).  `none` for an
    unknown symbol (OCaml: `Not_found`). -/
def delexSymbol (symbol : String) : Option String :=
  if symbol == "PRE_NAME" then some ""
  else (Terminal.all.find? (symbolName · == symbol)).map delex

/-- De-lexing a sentence: the symbols of `sentence` (separated by single
    spaces), each de-lexed and followed by a space. -/
def delexSentence (sentence : String) : Except String String := do
  let symbols := sentence.splitOn " "
  if symbols.getLast? == some "PRE_NAME" then
    throw "token sequence terminating with PRE_NAME"
  let strs ← symbols.mapM fun s => match delexSymbol s with
    | some c => pure c
    | none => throw s!"unknown symbol {s}"
  return String.join (strs.map (· ++ " "))

end DeLexer
end CC
