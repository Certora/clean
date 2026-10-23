/-
  Pretty-printer for Cminor — port of `backend/PrintCminor.ml`.

  The OCaml printer uses the `Format` module; here each printing function
  returns a `Format.Doc` (see `CCLib/lib/Format.lean`), and
  `printProgram` renders it to a string.  `print_if` (option `-dcminor`) is
  `printIf`, with the destination file as an argument.
-/
import CCLib.backend.Cminor
import CCLib.common.PrintAST
import CCLib.lib.Format

namespace CC
namespace PrintCminor

open Camlcoq PrintAST Format Cminor

/-! ## Precedences and associativity — like those of C -/

/-- `PrintCminor.associativity` -/
inductive Associativity where
  | LtoR | RtoL | NA
  deriving DecidableEq

/-- `PrintCminor.precedence` -/
def precedence : Cminor.Expr → Nat × Associativity
  | .Evar _ => (16, .NA)
  | .Econst _ => (16, .NA)
  | .Eunop _ _ => (15, .RtoL)
  | .Ebinop op _ _ =>
    match op with
    | .Omul | .Odiv | .Odivu | .Omod | .Omodu | .Omulf | .Odivf | .Omulfs | .Odivfs
    | .Omull | .Odivl | .Odivlu | .Omodl | .Omodlu => (13, .LtoR)
    | .Oadd | .Osub | .Oaddf | .Osubf | .Oaddfs | .Osubfs | .Oaddl | .Osubl => (12, .LtoR)
    | .Oshl | .Oshr | .Oshru | .Oshll | .Oshrl | .Oshrlu => (11, .LtoR)
    | .Ocmp _ | .Ocmpu _ | .Ocmpf _ | .Ocmpfs _ | .Ocmpl _ | .Ocmplu _ => (10, .LtoR)
    | .Oand | .Oandl => (8, .LtoR)
    | .Oxor | .Oxorl => (7, .LtoR)
    | .Oor | .Oorl => (6, .LtoR)
  | .Eload _ _ => (15, .RtoL)

/-! ## Reserved keywords and identifiers -/

/-- `PrintCminor.keywords` -/
def keywords : List String := [
  "absf", "abss", "any32", "any64",
  "builtin",
  "case",
  "default",
  "else", "exit", "extern",
  "float", "float32", "float64", "floatofint", "floatofintu",
    "floatoflong", "floatoflongu",
  "goto",
  "if", "int", "int16", "int16s", "int16u", "int32", "int64",
    "int8", "int8s", "int8u", "intoffloat", "intoflong",
    "intofsingle", "intuoffloat", "intuofsingle",
  "long", "longoffloat", "longofint", "longofintu", "longuoffloat", "loop",
  "match",
  "readonly", "return",
  "single", "singleofint", "singleofintu", "singleoflong", "singleoflongu",
  "stack", "switch", "switchl",
  "tailcall",
  "var", "void", "volatile",
  "while"]

/-- `re_ident`: `[A-Za-z_][A-Za-z_$0-9]*` or `$[1-9][0-9]*`. -/
def isPlainIdent (s : String) : Bool :=
  match s.toList with
  | c :: cs =>
    ((c.isAlpha || c == '_') && cs.all (fun c => c.isAlphanum || c == '_' || c == '$')) ||
    (c == '$' && match cs with
      | d :: ds => d.isDigit && d != '0' && ds.all Char.isDigit
      | [] => false)
  | [] => false

/-- `PrintCminor.ident_name` -/
def identName (id : Ident) : String :=
  let s := externAtom id
  if isPlainIdent s && !keywords.contains s then s else "'" ++ s ++ "'"

/-! ## Naming operators -/

/-- `PrintCminor.name_of_unop` -/
def nameOfUnop : UnaryOperation → String
  | .Ocast8unsigned => "int8u"
  | .Ocast8signed => "int8s"
  | .Ocast16unsigned => "int16u"
  | .Ocast16signed => "int16s"
  | .Onegint => "-"
  | .Onotint => "~"
  | .Onegf => "-f"
  | .Oabsf => "absf"
  | .Onegfs => "-s"
  | .Oabsfs => "abss"
  | .Osingleoffloat => "float32"
  | .Ofloatofsingle => "float64"
  | .Ointoffloat => "intoffloat"
  | .Ointuoffloat => "intuoffloat"
  | .Ofloatofint => "floatofint"
  | .Ofloatofintu => "floatofintu"
  | .Ointofsingle => "intofsingle"
  | .Ointuofsingle => "intuofsingle"
  | .Osingleofint => "singleofint"
  | .Osingleofintu => "singleofintu"
  | .Onegl => "-l"
  | .Onotl => "~l"
  | .Ointoflong => "intoflong"
  | .Olongofint => "longofint"
  | .Olongofintu => "longofintu"
  | .Olongoffloat => "longoffloat"
  | .Olonguoffloat => "longuoffloat"
  | .Ofloatoflong => "floatoflong"
  | .Ofloatoflongu => "floatoflongu"
  | .Olongofsingle => "longofsingle"
  | .Olonguofsingle => "longuofsingle"
  | .Osingleoflong => "singleoflong"
  | .Osingleoflongu => "singleoflongu"

/-- `PrintCminor.comparison_name` -/
abbrev comparisonName : Comparison → String := PrintAST.comparisonName

/-- `PrintCminor.name_of_binop` -/
def nameOfBinop : BinaryOperation → String
  | .Oadd => "+"
  | .Osub => "-"
  | .Omul => "*"
  | .Odiv => "/"
  | .Odivu => "/u"
  | .Omod => "%"
  | .Omodu => "%u"
  | .Oand => "&"
  | .Oor => "|"
  | .Oxor => "^"
  | .Oshl => "<<"
  | .Oshr => ">>"
  | .Oshru => ">>u"
  | .Oaddf => "+f"
  | .Osubf => "-f"
  | .Omulf => "*f"
  | .Odivf => "/f"
  | .Oaddfs => "+s"
  | .Osubfs => "-s"
  | .Omulfs => "*s"
  | .Odivfs => "/s"
  | .Oaddl => "+l"
  | .Osubl => "-l"
  | .Omull => "*l"
  | .Odivl => "/l"
  | .Odivlu => "/lu"
  | .Omodl => "%l"
  | .Omodlu => "%lu"
  | .Oandl => "&l"
  | .Oorl => "|l"
  | .Oxorl => "^l"
  | .Oshll => "<<l"
  | .Oshrl => ">>l"
  | .Oshrlu => ">>lu"
  | .Ocmp c => comparisonName c
  | .Ocmpu c => comparisonName c ++ "u"
  | .Ocmpf c => comparisonName c ++ "f"
  | .Ocmpfs c => comparisonName c ++ "s"
  | .Ocmpl c => comparisonName c ++ "l"
  | .Ocmplu c => comparisonName c ++ "lu"

/-! ## Expressions -/

/-- `PrintCminor.expr` -/
def expr (prec : Nat) (e : Cminor.Expr) : Doc :=
  let (prec', assoc) := precedence e
  let (prec1, prec2) := if assoc == .LtoR then (prec', prec' + 1) else (prec' + 1, prec')
  let body : Doc := match e with
    | .Evar id => txt (identName id)
    | .Econst (.Ointconst n) => txt (ci32 n)
    | .Econst (.Ofloatconst f) => txt (floatF f 15)
    | .Econst (.Osingleconst f) => txt (float32F f 15 ++ "f")
    | .Econst (.Olongconst n) => txt (ci64 n ++ "LL")
    | .Econst (.Oaddrsymbol id ofs) =>
      if wrapSigned 32 (CamlNum.toZ ofs) == 0 then txt s!"\"{externAtom id}\""
      else txt s!"(\"{externAtom id}\" + {ci32 ofs})"
    | .Econst (.Oaddrstack n) => txt s!"&{ci32 n}"
    | .Eunop op a1 => txt (nameOfUnop op ++ " ") ++ expr prec' a1
    | .Ebinop op a1 a2 =>
      expr prec1 a1 ++ ppf "@ " ++ txt (nameOfBinop op ++ " ") ++ expr prec2 a2
    | .Eload chunk a1 => txt (nameOfChunk chunk ++ "[") ++ expr 0 a1 ++ txt "]"
  (if prec' < prec then ppf "@[<hov 2>(" else ppf "@[<hov 2>") ++ body ++
  (if prec' < prec then ppf ")@]" else ppf "@]")

/-- `PrintCminor.print_expr` -/
def printExpr (e : Cminor.Expr) : Doc := expr 0 e

/-- `PrintCminor.print_expr_list` -/
def printExprList (first : Bool) : List Cminor.Expr → Doc
  | [] => #[]
  | r :: rl => (if first then #[] else ppf ",@ ") ++ expr 2 r ++ printExprList false rl

/-! ## Types -/

/-- `PrintCminor.print_sig` -/
def printSig (sg : Signature) : Doc :=
  (sg.sig_args.foldl (fun d t => d ++ txt (nameOfXtype t) ++ ppf " ->@ ") #[]) ++
  txt (nameOfXtype sg.sig_res)

/-- `PrintCminor.just_skips` -/
def justSkips : Cminor.Stmt → Bool
  | .Sskip => true
  | .Sseq s1 s2 => justSkips s1 && justSkips s2
  | _ => false

/-! ## Statements -/

/-- `PrintCminor.print_stmt` -/
def printStmt : Cminor.Stmt → Doc
  | .Sskip => txt "/*skip*/"
  | .Sassign id e2 => ppf "@[<hv 2>" ++ txt (identName id) ++ ppf " =@ " ++ printExpr e2 ++ ppf ";@]"
  | .Sstore chunk a1 a2 =>
    ppf "@[<hv 2>" ++ txt (nameOfChunk chunk) ++ txt "[" ++ printExpr a1 ++ ppf "] =@ " ++
      printExpr a2 ++ ppf ";@]"
  | .Scall none sg e1 el =>
    ppf "@[<hv 2>" ++ printExpr e1 ++ ppf "@,(@[<hov 0>" ++ printExprList true el ++
      ppf "@])@ : @[<hov 0>" ++ printSig sg ++ ppf "@];@]"
  | .Scall (some id) sg e1 el =>
    ppf "@[<hv 2>" ++ txt (identName id) ++ ppf " =@ " ++ printExpr e1 ++ ppf "@,(@[<hov 0>" ++
      printExprList true el ++ ppf "@])@] : @[<hov 0>" ++ printSig sg ++ ppf ";@]"
  | .Stailcall sg e1 el =>
    ppf "@[<hv 2>tailcall " ++ printExpr e1 ++ ppf "@,(@[<hov 0>" ++ printExprList true el ++
      ppf "@])@ : @[<hov 0>" ++ printSig sg ++ ppf "@];@]"
  | .Sbuiltin none ef el =>
    ppf "@[<hv 2>builtin " ++ txt (nameOfExternal ef) ++ ppf "@,(@[<hov 0>" ++
      printExprList true el ++ ppf "@])@ : @[<hov 0>" ++ printSig ef.sig ++ ppf "@];@]"
  | .Sbuiltin (some id) ef el =>
    ppf "@[<hv 2>" ++ txt (identName id) ++ ppf " =@ builtin " ++ txt (nameOfExternal ef) ++
      ppf "@,(@[<hov 0>" ++ printExprList true el ++ ppf "@]) : @[<hov 0>" ++
      printSig ef.sig ++ ppf "@];@]"
  | .Sseq s1 s2 =>
    if justSkips s1 && justSkips s2 then #[]
    else if justSkips s1 then printStmt s2
    else if justSkips s2 then printStmt s1
    else printStmt s1 ++ ppf "@ " ++ printStmt s2
  | .Sifthenelse e s1 .Sskip =>
    ppf "@[<v 2>if (" ++ printExpr e ++ ppf ") {@ " ++ printStmt s1 ++ ppf "@;<0 -2>}@]"
  | .Sifthenelse e s1 s2 =>
    ppf "@[<v 2>if (" ++ printExpr e ++ ppf ") {@ " ++ printStmt s1 ++
      ppf "@;<0 -2>} else {@ " ++ printStmt s2 ++ ppf "@;<0 -2>}@]"
  | .Sloop s => ppf "@[<v 2>loop {@ " ++ printStmt s ++ ppf "@;<0 -2>}@]"
  | .Sblock s => ppf "@[<v 3>{{ " ++ printStmt s ++ ppf "@;<0 -3>}}@]"
  | .Sexit n => txt s!"exit {n};"
  | .Sswitch long e cases dfl =>
    let printCase : Z × Nat → Doc := fun (n, x) =>
      if long then ppf "@ " ++ txt s!"case {wrapSigned 64 n}LL: exit {x};"
      else ppf "@ " ++ txt s!"case {wrapSigned 32 n}: exit {x};"
    ppf "@[<v 2>" ++ txt ("switch" ++ (if long then "l" else "") ++ " (") ++ printExpr e ++
      txt ") {" ++ (cases.foldl (fun d c => d ++ printCase c) #[]) ++
      ppf "@ " ++ txt s!"default: exit {dfl};\n" ++ ppf "@;<0 -2>}@]"
  | .Sreturn none => txt "return;"
  | .Sreturn (some e) => txt "return " ++ printExpr e ++ txt ";"
  | .Slabel lbl s1 => txt (identName lbl ++ ":") ++ ppf "@ " ++ printStmt s1
  | .Sgoto lbl => txt s!"goto {identName lbl};"

/-! ## Functions and programs -/

/-- `PrintCminor.print_varlist` -/
def printVarlist (first : Bool) : List Ident → Doc
  | [] => #[]
  | v1 :: vl => (if first then #[] else ppf ",@ ") ++ txt (identName v1) ++ printVarlist false vl

/-- `PrintCminor.print_function` -/
def printFunction (id : Ident) (f : Cminor.Function) : Doc :=
  let stksz := wrapSigned 32 f.fn_stackspace
  ppf "@[<hov 4>" ++ txt s!"\"{externAtom id}\"(" ++ ppf "@[<hov 0>" ++
    printVarlist true f.fn_params ++ ppf "@])@ : @[<hov 0>" ++ printSig f.fn_sig ++
    ppf "@]@]@ " ++
  ppf "@[<v 2>{@ " ++
  (if stksz ≠ 0 then txt s!"stack {stksz};" ++ ppf "@ " else #[]) ++
  (if f.fn_vars ≠ [] then ppf "var @[<hov 0>" ++ printVarlist true f.fn_vars ++ ppf ";@]@ "
   else #[]) ++
  printStmt f.fn_body ++
  ppf "@;<0 -2>}@]@ "

/-- `PrintCminor.print_extfun` -/
def printExtfun (id : Ident) (ef : ExtFun) : Doc :=
  ppf "@[<v 0>extern @[<hov 2>" ++ txt s!"\"{externAtom id}\" =" ++ ppf "@ " ++
    txt (nameOfExternal ef ++ " :") ++ ppf "@ " ++ printSig ef.sig ++ ppf "@]@]@ "

/-- `PrintCminor.print_init_data` -/
def printInitData : InitData → String
  | .Init_int8 i => s!"int8 {ci32 i}"
  | .Init_int16 i => s!"int16 {ci32 i}"
  | .Init_int32 i => ci32 i
  | .Init_int64 i => ci64 i ++ "LL"
  | .Init_float32 f => s!"float32 {float32F f 15}"
  | .Init_float64 f => floatF f 15
  | .Init_space i => s!"[{i}]"
  | .Init_addrof id off => s!"{ci32 off}(\"{externAtom id}\")"

/-- `PrintCminor.print_globvar` -/
def printGlobvar (gv : GlobVar Unit) : String :=
  (if gv.gvar_readonly then "readonly " else "") ++
  (if gv.gvar_volatile then "volatile " else "") ++
  "{" ++ ",".intercalate (gv.gvar_init.map printInitData) ++ "}"

/-- `PrintCminor.print_globdef` -/
def printGlobdef : Ident × GlobDef Cminor.Fundef Unit → Doc
  | (id, .Gfun (.External ef)) => printExtfun id ef
  | (id, .Gfun (.Internal f)) => printFunction id f
  | (id, .Gvar gv) => txt s!"var \"{externAtom id}\" {printGlobvar gv}\n"

/-- `PrintCminor.print_program`, as a document. -/
def programDoc (prog : Cminor.Program) : Doc :=
  ppf "@[<v 0>" ++
  (if externAtom prog.prog_main ≠ "main" then txt s!"= \"{externAtom prog.prog_main}\"\n"
   else #[]) ++
  (prog.prog_defs.foldl (fun d g => d ++ printGlobdef g) #[]) ++
  ppf "@]@."

/-- `PrintCminor.print_program` -/
def printProgram (prog : Cminor.Program) : String := render (programDoc prog)

/-- `PrintCminor.print_if` -/
def printIf (destination : Option String) (prog : Cminor.Program) : IO Unit :=
  match destination with
  | none => pure ()
  | some f => IO.FS.writeFile f (printProgram prog)

#guard identName (identOfString "x") = "x"
#guard identName (identOfString "loop") = "'loop'"
#guard identName (identOfString "a.b") = "'a.b'"

end PrintCminor
end CC
