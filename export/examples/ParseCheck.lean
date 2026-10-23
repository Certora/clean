/-
  Checks of the ported C front end from text: the lexer
  (`CCLib.cparser.Lexer`), the pre-parser that classifies identifiers
  (`CCLib.cparser.PreParser`), and `Parse.preprocessed_file` (lexing,
  pre-parsing, verified parser, elaboration, transformations) for x86-64.
  The `#guard`s run when this file is built.
-/
import CCLib.cparser.Parse
import CCLib.cparser.deLexer
import CCLib.x86.CBuiltins

namespace CC.ParseCheck

open CC CParser

/-- The classified identifiers of a text (`V` variable, `T` typedef,
    `O` other name), or the error messages. -/
def classify (src : String) : List String ⊕ List String :=
  let x : M (List String) := do
    let toks ← PreParser.tokens_stream ["__builtin_va_list"] "t.c" src.toUTF8
    return toks.toList.filterMap fun t => match t with
      | .VAR_NAME (s, _) => some ("V:" ++ s)
      | .TYPEDEF_NAME (s, _) => some ("T:" ++ s)
      | .OTHER_NAME (s, _) => some ("O:" ++ s)
      | _ => none
  match x.run { config := Machine.x86_64 } with
  | .ok r _ => .inr r
  | .error _ st => .inl st.messages.toList

/-- The front end on a text: the elaborated program printed by `Cprint`,
    or the messages. -/
def front (src : String) (o : Parse.Options := {}) : List String ⊕ String :=
  let x : M String := do
    let init ← Env.set_builtins (X86.CBuiltins.builtins true false)
    let p ← Parse.preprocessed_file o init "t.c" src.toUTF8
    return Cprint.toText (Cprint.program {} p)
  match x.run { config := Machine.x86_64 } with
  | .ok r _ => .inr r
  | .error _ st => .inl st.messages.toList

/-- The tokens' kinds and lines, for lexer checks. -/
def lexLines (src : String) : List (String × Int) :=
  match (Lexer.tokenize "t.c" src.toUTF8).run { config := Machine.x86_64 } with
  | .ok a _ => a.toList.map fun r =>
      (match r.name with
       | some id => id
       | none => match r.tok with
         | .PRAGMA (s, _) => "#pragma " ++ s
         | .CONSTANT (.CONST_INT s, _) => s
         | .EOF _ => "EOF"
         | _ => "_", r.loc.lineno)
  | .error _ _ => []

/-! ### Lexer -/

-- line directives and pragmas
#guard lexLines "int x;\n# 10 \"foo.h\"\ny 1\n#pragma pack(1)\nz\n" ==
  [("_", 1), ("x", 1), ("_", 1), ("y", 10), ("1", 10), ("#pragma pack(1)", 11), ("z", 12),
   ("EOF", 13)]

-- comments, digraphs, `__extension__`
#guard lexLines "/* a\n b */ x // c\n<% __extension__ y %>" ==
  [("x", 2), ("_", 3), ("y", 3), ("_", 3), ("EOF", 3)]

/-- The constants of a text. -/
def consts (src : String) : List Cabs.Constant :=
  match (Lexer.tokenize "t.c" src.toUTF8).run { config := Machine.x86_64 } with
  | .ok a _ => a.toList.filterMap fun r => match r.tok with
      | .CONSTANT (c, _) => some c
      | .STRING_LITERAL ((e, l), _) => some (.CONST_STRING e l)
      | _ => none
  | .error _ _ => []

#guard consts "0x1fUL 017 1.5e-3f .5 1. 0x1.8p-1L" ==
  [.CONST_INT "0x1fUL", .CONST_INT "017",
   .CONST_FLOAT { isHex_FI := false, integer_FI := some "1", fraction_FI := some "5",
                  exponent_FI := some "-3", suffix_FI := some "f" },
   .CONST_FLOAT { isHex_FI := false, integer_FI := none, fraction_FI := some "5",
                  exponent_FI := none, suffix_FI := none },
   .CONST_FLOAT { isHex_FI := false, integer_FI := some "1", fraction_FI := none,
                  exponent_FI := none, suffix_FI := none },
   .CONST_FLOAT { isHex_FI := true, integer_FI := some "1", fraction_FI := some "8",
                  exponent_FI := some "-1", suffix_FI := some "L" }]

-- escapes and encodings: UTF-8 for plain strings, UTF-16 for `u`, code
-- points for `U` and for `L` (32-bit `wchar_t` on x86-64)
#guard consts "'a' '\\n' '\\377' \"\\u00e9\\x41\" u\"\\U0001F600\" U\"\\U0001F600\" L\"é\"" ==
  [.CONST_CHAR .EncNone [97], .CONST_CHAR .EncNone [10], .CONST_CHAR .EncNone [255],
   .CONST_STRING .EncNone [195, 169, 65], .CONST_STRING .EncU16 [55357, 56832],
   .CONST_STRING .EncU32 [128512], .CONST_STRING .EncWide [233]]

-- an invalid preprocessing number is reported (and read as 0)
#guard match (Lexer.tokenize "t.c" "08".toUTF8).run { config := Machine.x86_64 } with
  | .ok _ st => st.num_errors == 1
  | .error _ _ => false

/-! ### Classification of identifiers -/

-- a typedef name used as a declarator, a label, a struct tag and a field;
-- `int f(int (t))` declares a parameter of type "function taking `t`"
#guard classify "typedef int t; int f(int (t)); int g(int (x)); void h(void) { t: ; goto t; } struct t { t t; } s;" ==
  .inr ["V:t", "V:f", "T:t", "V:g", "V:x", "V:h", "O:t", "O:t", "O:t", "T:t", "V:t", "V:s"]

-- scopes: blocks, `for` declarations, parameters
#guard classify "typedef int T; void f(T T); T x; void g(void) { T y; { int T; T = 1; } T z; for (int T = 0; T < 1; ) ; T w; }" ==
  .inr ["V:T", "V:f", "T:T", "V:T", "T:T", "V:x", "V:g", "T:T", "V:y", "V:T", "V:T", "T:T",
       "V:z", "V:T", "V:T", "T:T", "V:w"]

-- function definitions: the parameters are in scope in the body only;
-- K&R definitions; `if`/`else` scopes
#guard classify "typedef int T; int f(T) { return 0; } int f2(T a) { T b; return a; } int f3(a) T a; { return a; } void f4(void) { if (1) { typedef char T; T c; } else { T d; } T e; }" ==
  .inr ["V:T", "V:f", "T:T", "V:f2", "T:T", "V:a", "T:T", "V:b", "V:a", "V:f3", "V:a", "T:T",
       "V:a", "V:a", "V:f4", "V:T", "T:T", "V:c", "T:T", "V:d", "T:T", "V:e"]

#guard classify "typedef int T; int f5(int T) { return T; } T g; void f6(int a) { typedef int a; a b; } T i;" ==
  .inr ["V:T", "V:f5", "V:T", "V:T", "T:T", "V:g", "V:f6", "V:a", "V:a", "T:a", "V:b", "T:T", "V:i"]

-- attributes, compound literals, `offsetof`
#guard classify "typedef int T; int x __attribute__((aligned(8), mode(T, x))); struct s { int a; }; int y = ((struct s){1}).a; int z = __builtin_offsetof(struct s, a);" ==
  .inr ["V:T", "V:x", "O:aligned", "O:mode", "V:T", "V:x", "O:s", "V:a", "V:y", "O:s", "O:a",
       "V:z", "O:s", "O:a"]

-- builtin typedefs
#guard classify "__builtin_va_list ap;" == .inr ["T:__builtin_va_list", "V:ap"]

-- syntax errors
#guard classify "int x = ;" ==
  .inl ["t.c:1:9: syntax error after '=' and before ';'.\nFatal error; compilation aborted."]
#guard classify "typedef int T; void f(void) { if (1) ; else T d; }" ==
  .inl ["t.c:1:45: syntax error after 'else' and before 'T'.\nFatal error; compilation aborted."]

/-! ### The whole front end -/

#guard front "typedef int t;\nint f(t a) { t b = a; { int t = 3; b += t; } return b + (t)1; }\nchar *s = \"ab\" \"cd\";\n" ==
  .inr "typedef int t;\n\nint f(t a)\n{\n  t b = a;\n  {\n    int t__1 = 3;\n    b += t__1;\n  }\n  return b + (t) 1;\n}\n\nchar * s = \"abcd\";\n\n\n"

-- elaboration errors are reported with the locations given by the lexer
#guard front "int f(void) { return x; }" ==
  .inl ["t.c:1: error: use of undeclared identifier 'x'"]

-- backslash-newline sequences are rejected
#guard front "int x;\\\nint y;" ==
  .inl ["t.c: error: illegal backslash-newline sequence in preprocessed source",
          "1 error detected."]

/-! ### De-lexing (`CCLib.cparser.deLexer`) -/

/-- The terminals of the raw tokens of a text, with the identifiers
    (which the pre-parser classifies later) as `VAR_NAME`. -/
def lexTerms (src : String) : Option (List Parser.Terminal) :=
  match (Lexer.tokenize "t.c" src.toUTF8).run { config := Machine.x86_64 } with
  | .ok a _ => some (a.toList.map fun r => if r.name.isSome then .VAR_NAME else r.tok.term)
  | .error _ _ => none

/-- The lexer reads `delex t` back as `t` (then `EOF`); a typedef name is an
    identifier for the lexer, and `OTHER_NAME` and `EOF` de-lex to nothing. -/
def delexRoundTrip (t : Parser.Terminal) : Bool :=
  let expected : List Parser.Terminal := match t with
    | .TYPEDEF_NAME => [.VAR_NAME, .EOF]
    | .OTHER_NAME | .EOF => [.EOF]
    | _ => [t, .EOF]
  (lexTerms (DeLexer.delex t)).map (·.map Parser.Terminal.toNat)
    == some (expected.map Parser.Terminal.toNat)

#guard Parser.Terminal.all.all delexRoundTrip

#guard DeLexer.delexSentence "INT VAR_NAME EQ CONSTANT SEMICOLON" matches .ok "int x = 42 ; "
#guard DeLexer.delexSentence "IF LPAREN PRE_NAME" matches
  .error "token sequence terminating with PRE_NAME"
#guard DeLexer.delexSentence "IF FOO" matches .error "unknown symbol FOO"

end CC.ParseCheck
