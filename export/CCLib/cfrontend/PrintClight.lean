/-
  Pretty-printer for Clight — port of `cfrontend/PrintClight.ml`.

  The OCaml printer uses the `Format` module; here each printing function
  returns a `Format.Doc` (see `CCLib/lib/Format.lean`) and `printProgram`
  renders the program to a string.  It reuses the declarators, values and
  global-variable printers of `CCLib/cfrontend/PrintCsyntax.lean`.
  `print_if` (Clight1, option `-dclight`) and `print_if_2` (Clight2, used by
  `clightgen`) are `printIf` and `printIf2`, with the destination file as
  an argument.

  Differences: as in `PrintCsyntax`, the `C2C` information on globals is
  the argument `info`.  `temp_name` looks the identifier up in the
  string encoding of identifiers (`Camlcoq.externAtom`) instead of the
  OCaml table of atoms.
-/
import CCLib.cfrontend.PrintCsyntax
import CCLib.cfrontend.Clight

namespace CC
namespace PrintClight

open Camlcoq PrintAST Format PrintCsyntax

/-- `PrintClight.temp_name`: `$name` for a temporary that comes from a
    named variable, `$N` otherwise. -/
def tempName (id : Ident) : String :=
  match decodeIdent (posSize id) id with
  | some cs => "$" ++ String.ofList cs
  | none => "$" ++ toString id.toNat

/-- `PrintClight.precedence` -/
def precedence : Expr → Nat × Associativity
  | .Evar .. => (16, .NA)
  | .Etempvar .. => (16, .NA)
  | .Ederef .. => (15, .RtoL)
  | .Efield .. => (16, .LtoR)
  | .Econst_int .. => (16, .NA)
  | .Econst_float .. => (16, .NA)
  | .Econst_single .. => (16, .NA)
  | .Econst_long .. => (16, .NA)
  | .Esizeof .. => (15, .RtoL)
  | .Ealignof .. => (15, .RtoL)
  | .Eunop .. => (15, .RtoL)
  | .Eaddrof .. => (15, .RtoL)
  | .Ecast .. => (14, .RtoL)
  | .Ebinop op _ _ _ =>
    match op with
    | .Omul | .Odiv | .Omod => (13, .LtoR)
    | .Oadd | .Osub => (12, .LtoR)
    | .Oshl | .Oshr => (11, .LtoR)
    | .Olt | .Ogt | .Ole | .Oge => (10, .LtoR)
    | .Oeq | .One => (9, .LtoR)
    | .Oand => (8, .LtoR)
    | .Oxor => (7, .LtoR)
    | .Oor => (6, .LtoR)

/-- `%.18g` of a binary64 float. -/
def floatG18 (f : Floats.Float) : String :=
  formatG 18 (decodeIEEE 11 52 (Integers.Int64.unsigned f.toBits).toNat)

/-- `%.18g` of a binary32 float. -/
def float32G18 (f : Floats.Float32) : String :=
  formatG 18 (decodeIEEE 8 23 (Integers.Int.unsigned f.toBits).toNat)

/-- `PrintClight.expr` -/
def expr (prec : Nat) (e : Expr) : Doc :=
  let (prec', assoc) := precedence e
  let (prec1, prec2) := if assoc == .LtoR then (prec', prec' + 1) else (prec' + 1, prec')
  let body : Doc := match e with
    | .Evar id _ => txt (externAtom id)
    | .Etempvar id _ => txt (tempName id)
    | .Ederef a1 _ => txt "*" ++ expr prec' a1
    | .Efield a1 f _ => expr prec' a1 ++ txt ("." ++ externAtom f)
    | .Econst_int n (.Tint .I32 .Unsigned _) => txt (cu32 n ++ "U")
    | .Econst_int n _ => txt (ci32 n)
    | .Econst_float f _ => txt (floatG18 f)
    | .Econst_single f _ => txt (float32G18 f ++ "f")
    | .Econst_long n (.Tlong .Unsigned _) => txt (cu64 n ++ "LLU")
    | .Econst_long n _ => txt (ci64 n ++ "LL")
    | .Eunop .Oabsfloat a1 _ => txt "__builtin_fabs(" ++ expr 2 a1 ++ txt ")"
    | .Eunop op a1 _ => txt (nameUnop op) ++ expr prec' a1
    | .Eaddrof a1 _ => txt "&" ++ expr prec' a1
    | .Ebinop op a1 a2 _ =>
      expr prec1 a1 ++ ppf "@ " ++ txt (nameBinop op ++ " ") ++ expr prec2 a2
    | .Ecast a1 ty => txt s!"({nameType ty}) " ++ expr prec' a1
    | .Esizeof ty _ => txt s!"sizeof({nameType ty})"
    | .Ealignof ty _ => txt s!"__alignof__({nameType ty})"
  (if prec' < prec then ppf "@[<hov 2>(" else ppf "@[<hov 2>") ++ body ++
  (if prec' < prec then ppf ")@]" else ppf "@]")

/-- `PrintClight.print_expr` -/
def printExpr (e : Expr) : Doc := expr 0 e

/-- `PrintClight.print_expr_list` -/
def printExprList (first : Bool) : List Expr → Doc
  | [] => #[]
  | r :: rl => (if first then #[] else ppf ",@ ") ++ expr 2 r ++ printExprList false rl

mutual
/-- `PrintClight.print_stmt` -/
def printStmt : Stmt → Doc
  | .Sskip => txt "/*skip*/;"
  | .Sassign e1 e2 => ppf "@[<hv 2>" ++ printExpr e1 ++ ppf " =@ " ++ printExpr e2 ++ ppf ";@]"
  | .Sset id e2 => ppf "@[<hv 2>" ++ txt (tempName id) ++ ppf " =@ " ++ printExpr e2 ++ ppf ";@]"
  | .Scall none e1 el =>
    ppf "@[<hv 2>" ++ expr 15 e1 ++ ppf "@,(@[<hov 0>" ++ printExprList true el ++ ppf "@]);@]"
  | .Scall (some id) e1 el =>
    ppf "@[<hv 2>" ++ txt (tempName id) ++ ppf " =@ " ++ expr 15 e1 ++ ppf "@,(@[<hov 0>" ++
      printExprList true el ++ ppf "@]);@]"
  | .Sbuiltin none ef _ el =>
    ppf "@[<hv 2>builtin " ++ txt (nameOfExternal ef) ++ ppf "@,(@[<hov 0>" ++
      printExprList true el ++ ppf "@]);@]"
  | .Sbuiltin (some id) ef _ el =>
    ppf "@[<hv 2>" ++ txt (tempName id) ++ ppf " =@ builtin " ++ txt (nameOfExternal ef) ++
      ppf "@,(@[<hov 0>" ++ printExprList true el ++ ppf "@]);@]"
  | .Ssequence .Sskip s2 => printStmt s2
  | .Ssequence s1 .Sskip => printStmt s1
  | .Ssequence s1 s2 => printStmt s1 ++ ppf "@ " ++ printStmt s2
  | .Sifthenelse e s1 .Sskip =>
    ppf "@[<v 2>if (" ++ printExpr e ++ ppf ") {@ " ++ printStmt s1 ++ ppf "@;<0 -2>}@]"
  | .Sifthenelse e .Sskip s2 =>
    ppf "@[<v 2>if (! " ++ expr 15 e ++ ppf ") {@ " ++ printStmt s2 ++ ppf "@;<0 -2>}@]"
  | .Sifthenelse e s1 s2 =>
    ppf "@[<v 2>if (" ++ printExpr e ++ ppf ") {@ " ++ printStmt s1 ++
      ppf "@;<0 -2>} else {@ " ++ printStmt s2 ++ ppf "@;<0 -2>}@]"
  | .Sloop s1 .Sskip => ppf "@[<v 2>while (1) {@ " ++ printStmt s1 ++ ppf "@;<0 -2>}@]"
  | .Sloop s1 s2 =>
    ppf "@[<v 2>for (@[<hv 0>;@ 1;@ " ++ printStmtFor s2 ++ ppf ") {@]@ " ++ printStmt s1 ++
      ppf "@;<0 -2>}@]"
  | .Sbreak => txt "break;"
  | .Scontinue => txt "continue;"
  | .Sswitch e cases =>
    ppf "@[<v 2>switch (" ++ printExpr e ++ ppf ") {@ " ++ printCases cases ++
      ppf "@;<0 -2>}@]"
  | .Sreturn none => txt "return;"
  | .Sreturn (some e) => txt "return " ++ printExpr e ++ txt ";"
  | .Slabel lbl s1 => txt (externAtom lbl ++ ":") ++ ppf "@ " ++ printStmt s1
  | .Sgoto lbl => txt s!"goto {externAtom lbl};"

/-- `PrintClight.print_cases` -/
def printCases : LStmts → Doc
  | .LSnil => #[]
  | .LScons lbl .Sskip rem => txt (printCaseLabel lbl ++ ":") ++ ppf "@ " ++ printCases rem
  | .LScons lbl s rem =>
    ppf "@[<v 2>" ++ txt (printCaseLabel lbl ++ ":") ++ ppf "@ " ++ printStmt s ++ ppf "@]@ " ++
      printCases rem

/-- `PrintClight.print_stmt_for` -/
def printStmtFor : Stmt → Doc
  | .Sskip => txt "(void)0"
  | .Sassign e1 e2 => printExpr e1 ++ txt " = " ++ printExpr e2
  | .Sset id e2 => txt (tempName id ++ " = ") ++ printExpr e2
  | .Ssequence .Sskip s2 => printStmtFor s2
  | .Ssequence s1 s2 => printStmtFor s1 ++ txt ", " ++ printStmtFor s2
  | .Scall none e1 el =>
    ppf "@[<hv 2>" ++ expr 15 e1 ++ ppf "@,(@[<hov 0>" ++ printExprList true el ++ ppf "@])@]"
  | .Scall (some id) e1 el =>
    ppf "@[<hv 2>" ++ txt (tempName id) ++ ppf " =@ " ++ expr 15 e1 ++ ppf "@,(@[<hov 0>" ++
      printExprList true el ++ ppf "@])@]"
  | .Sbuiltin none ef _ el =>
    ppf "@[<hv 2>builtin " ++ txt (nameOfExternal ef) ++ ppf "@,(@[<hov 0>" ++
      printExprList true el ++ ppf "@]);@]"
  | .Sbuiltin (some id) ef _ el =>
    ppf "@[<hv 2>" ++ txt (tempName id) ++ ppf " =@ builtin " ++ txt (nameOfExternal ef) ++
      ppf "@,(@[<hov 0>" ++ printExprList true el ++ ppf "@]);@]"
  | s => txt "({ " ++ printStmt s ++ txt " })"
end

/-- `PrintClight.clight_version`: in Clight1 function parameters are
    variables, in Clight2 they are temporaries. -/
inductive ClightVersion where
  | Clight1 | Clight2
  deriving DecidableEq

/-- `PrintClight.name_param` -/
def nameParam : ClightVersion → Ident → String
  | .Clight1 => externAtom
  | .Clight2 => tempName

/-- `PrintClight.print_function` -/
def printFunction (ver : ClightVersion) (id : Ident) (f : Function) : Doc :=
  txt (nameCdecl (nameFunctionParameters (nameParam ver) (externAtom id) f.fn_params
    f.fn_callconv) f.fn_return) ++ ppf "@ " ++
  ppf "@[<v 2>{@ " ++
  (f.fn_vars.foldl (fun d (id, ty) => d ++ txt (nameCdecl (externAtom id) ty ++ ";") ++ ppf "@ ")
    #[]) ++
  (f.fn_temps.foldl (fun d (id, ty) =>
    d ++ txt ("register " ++ nameCdecl (tempName id) ty ++ ";") ++ ppf "@ ") #[]) ++
  printStmt f.fn_body ++
  ppf "@;<0 -2>}@]@ @ "

/-- `PrintClight.print_fundef` -/
def printFundef (ver : ClightVersion) (id : Ident) : FunDef → Doc
  | .External .. => #[]
  | .Internal f => printFunction ver id f

/-- `PrintClight.print_fundecl` -/
def printFundecl (id : Ident) : FunDef → Doc
  | .External ef args res cconv =>
    match ef with
    | .EF_external .. | .EF_runtime .. | .EF_malloc | .EF_free =>
      txt s!"extern {nameCdecl (externAtom id) (.Tfunction args res cconv)};" ++ ppf "@ "
    | _ => #[]
  | .Internal f => txt s!"{nameCdecl (externAtom id) (typeOfFunction f)};" ++ ppf "@ "

/-- `PrintClight.print_globdef` -/
def printGlobdef (info : AtomInfo) (ver : ClightVersion) : Ident × GlobDef FunDef Ty → Doc
  | (id, .Gfun f) => printFundef ver id f
  | (id, .Gvar v) => printGlobvar info id v

/-- `PrintClight.print_globdecl` -/
def printGlobdecl : Ident × GlobDef FunDef Ty → Doc
  | (id, .Gfun f) => printFundecl id f
  | (_, .Gvar _) => #[]

/-- `PrintClight.print_program`, as a document. -/
def programDoc (ver : ClightVersion) (info : AtomInfo) (prog : Program) : Doc :=
  ppf "@[<v 0>" ++
  (prog.prog_types.foldl (fun d c => d ++ declareComposite c) #[]) ++
  (prog.prog_types.foldl (fun d c => d ++ defineComposite c) #[]) ++
  (prog.prog_defs.foldl (fun d g => d ++ printGlobdecl g) #[]) ++
  (prog.prog_defs.foldl (fun d g => d ++ printGlobdef info ver g) #[]) ++
  ppf "@]@."

/-- `PrintClight.print_program` -/
def printProgram (ver : ClightVersion) (prog : Program) (info : AtomInfo := {}) : String :=
  render (programDoc ver info prog)

/-- `PrintClight.print_if_gen` -/
def printIfGen (ver : ClightVersion) (destination : Option String) (prog : Program)
    (info : AtomInfo := {}) : IO Unit :=
  match destination with
  | none => pure ()
  | some f => IO.FS.writeFile f (printProgram ver prog info)

/-- `PrintClight.print_if` (Clight1, between `SimplExpr` and `SimplLocals`) -/
def printIf (destination : Option String) (prog : Program) (info : AtomInfo := {}) : IO Unit :=
  printIfGen .Clight1 destination prog info

/-- `PrintClight.print_if_2` (Clight2, after `SimplLocals`) -/
def printIf2 (destination : Option String) (prog : Program) (info : AtomInfo := {}) : IO Unit :=
  printIfGen .Clight2 destination prog info

end PrintClight
end CC
