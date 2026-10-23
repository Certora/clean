/-
  Pretty-printer for Csyntax (CompCert C) — port of
  `cfrontend/PrintCsyntax.ml`.

  The OCaml printer uses the `Format` module; here each printing function
  returns a `Format.Doc` (see `CCLib/lib/Format.lean`) and `printProgram`
  renders the program to a string.  `print_if` (option `-dc`) is `printIf`,
  with the destination file as an argument.

  Differences:
  * The OCaml printer asks the front end (`C2C.atom_is_static`,
    `C2C.atom_literal`) whether a global is `static` and whether it is a
    string literal.  `C2C` is not ported; this information is the argument
    `info : AtomInfo` (by default: nothing is static, nothing is a string
    literal).
  * `print_pointer_hook` is the default hook, which prints nothing (so
    pointers print as `<ptr>` and locations as `<loc>`).
-/
import CCLib.cfrontend.Csyntax
import CCLib.common.PrintAST
import CCLib.lib.Format

namespace CC
namespace PrintCsyntax

open Camlcoq PrintAST Format

/-- What the OCaml printers learn from `C2C` about a global. -/
structure AtomInfo where
  /-- `C2C.atom_is_static` -/
  isStatic : Ident → Bool := fun _ => false
  /-- `C2C.atom_literal id = C2C.String_literal` -/
  isStringLiteral : Ident → Bool := fun _ => false

instance : Inhabited AtomInfo := ⟨{}⟩

/-- `PrintCsyntax.name_unop` -/
def nameUnop : Unop → String
  | .Onotbool => "!"
  | .Onotint => "~"
  | .Oneg => "-"
  | .Oabsfloat => "__builtin_fabs"

/-- `PrintCsyntax.name_binop` -/
def nameBinop : Binop → String
  | .Oadd => "+"
  | .Osub => "-"
  | .Omul => "*"
  | .Odiv => "/"
  | .Omod => "%"
  | .Oand => "&"
  | .Oor => "|"
  | .Oxor => "^"
  | .Oshl => "<<"
  | .Oshr => ">>"
  | .Oeq => "=="
  | .One => "!="
  | .Olt => "<"
  | .Ogt => ">"
  | .Ole => "<="
  | .Oge => ">="

/-- `PrintCsyntax.name_inttype` -/
def nameInttype : IntSize → Signedness → String
  | .I8, .Signed => "signed char"
  | .I8, .Unsigned => "unsigned char"
  | .I16, .Signed => "short"
  | .I16, .Unsigned => "unsigned short"
  | .I32, .Signed => "int"
  | .I32, .Unsigned => "unsigned int"
  | .IBool, _ => "_Bool"

/-- `PrintCsyntax.name_floattype` -/
def nameFloattype : FloatSize → String
  | .F32 => "float"
  | .F64 => "double"

/-- `PrintCsyntax.name_longtype` -/
def nameLongtype : Signedness → String
  | .Signed => "long long"
  | .Unsigned => "unsigned long long"

/-! ## Declarators (identifier + type) -/

/-- `PrintCsyntax.attributes` -/
def attributes (a : Attr) : String :=
  let s1 := if a.attr_volatile then " volatile" else ""
  match a.attr_alignas with
  | none => s1
  | some l => s!" _Alignas({wrapSigned 64 (2 ^ l : Nat)}){s1}"

/-- `PrintCsyntax.attributes_space` -/
def attributesSpace (a : Attr) : String :=
  let s := attributes a
  if s.isEmpty then s else s ++ " "

/-- `PrintCsyntax.name_optid` -/
def nameOptid (id : String) : String := if id.isEmpty then "" else " " ++ id

mutual
/-- `PrintCsyntax.name_cdecl` -/
def nameCdecl (id : String) : Ty → String
  | .Tvoid => "void" ++ nameOptid id
  | .Tint sz sg a => nameInttype sz sg ++ attributes a ++ nameOptid id
  | .Tfloat sz a => nameFloattype sz ++ attributes a ++ nameOptid id
  | .Tlong sg a => nameLongtype sg ++ attributes a ++ nameOptid id
  | .Tpointer t a =>
    let id' := match t with
      | .Tfunction .. | .Tarray .. => s!"(*{attributesSpace a}{id})"
      | _ => s!"*{attributesSpace a}{id}"
    nameCdecl id' t
  | .Tarray t n _ => nameCdecl s!"{id}[{ci32 n}]" t
  | .Tfunction args res cconv =>
    let head := (if id.isEmpty then "(*)" else id) ++ "("
    let body := if cconv.cc_unproto then "" else nameArgs true cconv args
    nameCdecl (head ++ body ++ ")") res
  | .Tstruct name a => "struct " ++ externAtom name ++ attributes a ++ nameOptid id
  | .Tunion name a => "union " ++ externAtom name ++ attributes a ++ nameOptid id

/-- The argument list of a function declarator (`add_args`). -/
def nameArgs (first : Bool) (cconv : CallConv) : List Ty → String
  | [] =>
    if first then (if cconv.cc_vararg.isSome then "..." else "void")
    else if cconv.cc_vararg.isSome then ", ..."
    else ""
  | t1 :: tl => (if first then "" else ", ") ++ nameCdecl "" t1 ++ nameArgs false cconv tl
end

/-- `PrintCsyntax.name_type` -/
def nameType (ty : Ty) : String := nameCdecl "" ty

/-! ## Precedences and associativity (H&S section 7.2) -/

/-- `PrintCsyntax.associativity` -/
inductive Associativity where
  | LtoR | RtoL | NA
  deriving DecidableEq

open Csyntax in
/-- `PrintCsyntax.precedence` -/
def precedence : Csyntax.Expr → Nat × Associativity
  | .Eloc .. => (16, .NA)
  | .Evar .. => (16, .NA)
  | .Ederef .. => (15, .RtoL)
  | .Efield .. => (16, .LtoR)
  | .Eval .. => (16, .NA)
  | .Evalof l _ => precedence l
  | .Esizeof .. => (15, .RtoL)
  | .Ealignof .. => (15, .RtoL)
  | .Ecall .. | .Ebuiltin .. => (16, .LtoR)
  | .Epostincr .. => (16, .LtoR)
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
  | .Eseqand .. => (5, .LtoR)
  | .Eseqor .. => (4, .LtoR)
  | .Econdition .. => (3, .RtoL)
  | .Eassign .. => (2, .RtoL)
  | .Eassignop .. => (2, .RtoL)
  | .Ecomma .. => (1, .LtoR)
  | .Eparen .. => (14, .RtoL)

/-! ## Expressions -/

/-- `PrintCsyntax.print_typed_value` -/
def printTypedValue (v : Val) (ty : Ty) : String :=
  match v, ty with
  | .Vint n, .Tint .I32 .Unsigned _ => cu32 n ++ "U"
  | .Vint n, _ => ci32 n
  | .Vfloat f, _ => floatF f 15
  | .Vsingle f, _ => float32F f 15 ++ "f"
  | .Vlong n, .Tlong .Unsigned _ => cu64 n ++ "LLU"
  | .Vlong n, _ => ci64 n ++ "LL"
  | .Vptr _ _, _ => "<ptr>"
  | .Vundef, _ => "<undef>"

/-- `PrintCsyntax.print_value` -/
def printValue (v : Val) : String := printTypedValue v .Tvoid

/-- `PrintCsyntax.extended_asm`, given the printed result and inputs. -/
def extendedAsm (text : String) (res : Option Doc) (inputs : List Doc)
    (clob : List String) : Doc :=
  ppf "asm volatile (@[<hv 0>" ++ txt (escapedString text) ++ ppf "@ :" ++
  (match res with
   | none => #[]
   | some e => txt " \"=r\"(" ++ e ++ txt ")") ++
  ppf "@ : @[<hov 0>" ++
  ((inputs.zipIdx.map fun (e, i) =>
      (if i == 0 then #[] else ppf ",@ ") ++ txt "\"r\"(" ++ e ++ txt ")").foldl (· ++ ·) #[]) ++
  ppf "@]" ++
  (match clob with
   | [] => #[]
   | c1 :: cl =>
     ppf "@ : @[<hov 0>" ++ txt (escapedString c1) ++
       (cl.foldl (fun d c => d ++ ppf ",@ " ++ txt (escapedString c)) #[]) ++ ppf "@]") ++
  ppf ")@]"

mutual
/-- `PrintCsyntax.expr` -/
def expr (prec : Nat) : Csyntax.Expr → Doc
  | .Evalof l _ =>
    -- `Evalof(l, _) -> expr p (prec, l)`, inside the box of `Evalof`
    let (prec', _) := precedence l
    (if prec' < prec then ppf "@[<hov 2>(" else ppf "@[<hov 2>") ++ expr prec l ++
    (if prec' < prec then ppf ")@]" else ppf "@]")
  | e =>
    let (prec', assoc) := precedence e
    let (prec1, prec2) := if assoc == .LtoR then (prec', prec' + 1) else (prec' + 1, prec')
    (if prec' < prec then ppf "@[<hov 2>(" else ppf "@[<hov 2>") ++ exprBody prec' prec1 prec2 e ++
    (if prec' < prec then ppf ")@]" else ppf "@]")

/-- The body of `expr` (the part between the parentheses). -/
def exprBody (prec' prec1 prec2 : Nat) : Csyntax.Expr → Doc
  | .Eloc .. => txt "<loc>"
  | .Evar id _ => txt (externAtom id)
  | .Ederef a1 _ => txt "*" ++ expr prec' a1
  | .Efield a1 f _ => expr prec' a1 ++ txt ("." ++ externAtom f)
  | .Evalof l _ => expr prec' l
  | .Eval v ty => txt (printTypedValue v ty)
  | .Esizeof ty _ => txt s!"sizeof({nameType ty})"
  | .Ealignof ty _ => txt s!"__alignof__({nameType ty})"
  | .Eunop .Oabsfloat a1 _ => txt "__builtin_fabs(" ++ expr 2 a1 ++ txt ")"
  | .Eunop op a1 _ => txt (nameUnop op) ++ expr prec' a1
  | .Eaddrof a1 _ => txt "&" ++ expr prec' a1
  | .Epostincr id a1 _ =>
    expr prec' a1 ++ txt (match id with | .Incr => "++" | .Decr => "--")
  | .Ebinop op a1 a2 _ =>
    expr prec1 a1 ++ ppf "@ " ++ txt (nameBinop op ++ " ") ++ expr prec2 a2
  | .Ecast a1 ty => txt s!"({nameType ty}) " ++ expr prec' a1
  | .Eassign res (.Ebuiltin (.EF_inline_asm text _ clob) _ args _) _ =>
    extendedAsm text (some (expr 0 res)) (exprItems args) clob
  | .Eassign a1 a2 _ => expr prec1 a1 ++ ppf " =@ " ++ expr prec2 a2
  | .Eassignop op a1 a2 _ _ =>
    expr prec1 a1 ++ txt s!" {nameBinop op}=" ++ ppf "@ " ++ expr prec2 a2
  | .Eseqand a1 a2 _ => expr prec1 a1 ++ ppf "@ && " ++ expr prec2 a2
  | .Eseqor a1 a2 _ => expr prec1 a1 ++ ppf "@ || " ++ expr prec2 a2
  | .Econdition a1 a2 a3 _ =>
    expr 4 a1 ++ ppf "@ ? " ++ expr 4 a2 ++ ppf "@ : " ++ expr 4 a3
  | .Ecomma a1 a2 _ => expr prec1 a1 ++ ppf ",@ " ++ expr prec2 a2
  | .Ecall a1 al _ => expr prec' a1 ++ ppf "@[<hov 1>(" ++ exprlist true al ++ ppf ")@]"
  | .Ebuiltin (.EF_memcpy sz al) _ args _ =>
    ppf "__builtin_memcpy_aligned@[<hov 1>(" ++ txt (ci32 sz) ++ ppf ",@ " ++ txt (ci32 al) ++
      ppf ",@ " ++ exprlist true args ++ ppf ")@]"
  | .Ebuiltin (.EF_annot _ text _) _ args _ =>
    ppf "__builtin_annot@[<hov 1>(" ++ txt (escapedString text) ++ exprlist false args ++
      ppf ")@]"
  | .Ebuiltin (.EF_annot_val _ text _) _ args _ =>
    ppf "__builtin_annot_intval@[<hov 1>(" ++ txt (escapedString text) ++
      exprlist false args ++ ppf ")@]"
  | .Ebuiltin (.EF_external id _) _ args _ =>
    txt id ++ ppf "@[<hov 1>(" ++ exprlist true args ++ ppf ")@]"
  | .Ebuiltin (.EF_runtime id _) _ args _ =>
    txt id ++ ppf "@[<hov 1>(" ++ exprlist true args ++ ppf ")@]"
  | .Ebuiltin (.EF_inline_asm text _ clob) _ args _ =>
    extendedAsm text none (exprItems args) clob
  | .Ebuiltin (.EF_debug kind text _) _ args _ =>
    ppf "__builtin_debug@[<hov 1>(" ++
      txt s!"{kind.toNat},{escapedString (externAtom text)}" ++ exprlist false args ++ ppf ")@]"
  | .Ebuiltin (.EF_builtin name _) _ args _ =>
    txt name ++ ppf "@[<hov 1>(" ++ exprlist true args ++ ppf ")@]"
  | .Ebuiltin _ _ args _ =>
    ppf "<unknown builtin>@[<hov 1>(" ++ exprlist true args ++ ppf ")@]"
  | .Eparen a1 tycast _ => txt s!"({nameType tycast}) " ++ expr prec' a1

/-- `PrintCsyntax.exprlist` -/
def exprlist (first : Bool) : Csyntax.ExprList → Doc
  | .Enil => #[]
  | .Econs r rl => (if first then #[] else ppf ",@ ") ++ expr 2 r ++ exprlist false rl

/-- The inputs of an inline `asm`, each printed with `expr p (0, e)`. -/
def exprItems : Csyntax.ExprList → List Doc
  | .Enil => []
  | .Econs r rl => expr 0 r :: exprItems rl
end

/-- `PrintCsyntax.print_expr` -/
def printExpr (e : Csyntax.Expr) : Doc := expr 0 e
/-- `PrintCsyntax.print_exprlist` -/
def printExprlist (el : Csyntax.ExprList) : Doc := exprlist true el

/-! ## Statements -/

/-- `PrintCsyntax.print_case_label` -/
def printCaseLabel : Option Z → String
  | none => "default"
  | some lbl => s!"case {lbl}"

mutual
/-- `PrintCsyntax.print_stmt` -/
def printStmt : Csyntax.Stmt → Doc
  | .Sskip => txt "/*skip*/;"
  | .Sdo e => printExpr e ++ txt ";"
  | .Ssequence s1 s2 => printStmt s1 ++ ppf "@ " ++ printStmt s2
  | .Sifthenelse e s1 .Sskip =>
    ppf "@[<v 2>if (" ++ printExpr e ++ ppf ") {@ " ++ printStmt s1 ++ ppf "@;<0 -2>}@]"
  | .Sifthenelse e s1 s2 =>
    ppf "@[<v 2>if (" ++ printExpr e ++ ppf ") {@ " ++ printStmt s1 ++
      ppf "@;<0 -2>} else {@ " ++ printStmt s2 ++ ppf "@;<0 -2>}@]"
  | .Swhile e s =>
    ppf "@[<v 2>while (" ++ printExpr e ++ ppf ") {@ " ++ printStmt s ++ ppf "@;<0 -2>}@]"
  | .Sdowhile e s =>
    ppf "@[<v 2>do {@ " ++ printStmt s ++ ppf "@;<0 -2>} while(" ++ printExpr e ++ ppf ");@]"
  | .Sfor sInit e sIter sBody =>
    ppf "@[<v 2>for (@[<hv 0>" ++ printStmtFor sInit ++ ppf ";@ " ++ printExpr e ++
      ppf ";@ " ++ printStmtFor sIter ++ ppf ") {@]@ " ++ printStmt sBody ++
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

/-- `PrintCsyntax.print_cases` -/
def printCases : Csyntax.LStmts → Doc
  | .LSnil => #[]
  | .LScons lbl .Sskip rem => txt (printCaseLabel lbl ++ ":") ++ ppf "@ " ++ printCases rem
  | .LScons lbl s rem =>
    ppf "@[<v 2>" ++ txt (printCaseLabel lbl ++ ":") ++ ppf "@ " ++ printStmt s ++ ppf "@]@ " ++
      printCases rem

/-- `PrintCsyntax.print_stmt_for` -/
def printStmtFor : Csyntax.Stmt → Doc
  | .Sskip => txt "/*nothing*/"
  | .Sdo e => printExpr e
  | .Ssequence s1 s2 => printStmtFor s1 ++ txt ", " ++ printStmtFor s2
  | s => txt "({ " ++ printStmt s ++ txt " })"
end

/-! ## Functions, global variables, composites -/

/-- `PrintCsyntax.name_function_parameters` -/
def nameFunctionParameters (nameParam : Ident → String) (funName : String)
    (params : List (Ident × Ty)) (cconv : CallConv) : String :=
  let body := match params with
    | [] => if cconv.cc_vararg.isSome then "..." else "void"
    | _ =>
      ", ".intercalate (params.map fun (id, ty) => nameCdecl (nameParam id) ty) ++
      (if cconv.cc_vararg.isSome then ",..." else "")
  funName ++ "(" ++ body ++ ")"

/-- `PrintCsyntax.print_function` -/
def printFunction (id : Ident) (f : Csyntax.Function) : Doc :=
  txt (nameCdecl (nameFunctionParameters externAtom (externAtom id) f.fn_params f.fn_callconv)
    f.fn_return) ++ ppf "@ " ++
  ppf "@[<v 2>{@ " ++
  (f.fn_vars.foldl (fun d (id, ty) => d ++ txt (nameCdecl (externAtom id) ty ++ ";") ++ ppf "@ ")
    #[]) ++
  printStmt f.fn_body ++
  ppf "@;<0 -2>}@]@ @ "

/-- `PrintCsyntax.print_fundef` -/
def printFundef (id : Ident) : Csyntax.FunDef → Doc
  | .External ef args res cconv =>
    match ef with
    | .EF_external .. | .EF_runtime .. | .EF_malloc | .EF_free =>
      txt s!"extern {nameCdecl (externAtom id) (.Tfunction args res cconv)};" ++ ppf "@ @ "
    | _ => #[]
  | .Internal f => printFunction id f

/-- `PrintCsyntax.print_fundecl` -/
def printFundecl (info : AtomInfo) (id : Ident) : Csyntax.FunDef → Doc
  | .Internal f =>
    let linkage := if info.isStatic id then "static" else "extern"
    txt s!"{linkage} {nameCdecl (externAtom id) (Csyntax.typeOfFunction f)};" ++ ppf "@ @ "
  | _ => #[]

/-- `PrintCsyntax.string_of_init` (only `Init_int8` initializers; others
    print as `?`, where OCaml fails with `assert false`). -/
def stringOfInit (il : List InitData) : String :=
  String.join (il.map fun i => match i with
    | .Init_int8 n =>
      let c := (Integers.Int.unsigned n).toNat % 256
      if c ≥ 32 && c ≤ 126 && c != 34 && c != 92 then String.singleton (Char.ofNat c)
      else "\\" ++ padZeros 3 (String.ofList (Nat.toDigits 8 c))
    | _ => "?")

/-- `PrintCsyntax.chop_last_nul` -/
def chopLastNul (il : List InitData) : List InitData :=
  match il.reverse with
  | .Init_int8 n :: tl => if Integers.Int.unsigned n == 0 then tl.reverse else il
  | _ => il

/-- `PrintCsyntax.print_init` -/
def printInit : InitData → Doc
  | .Init_int8 n => txt (ci32 n)
  | .Init_int16 n => txt (ci32 n)
  | .Init_int32 n => txt (ci32 n)
  | .Init_int64 n => txt (ci64 n ++ "LL")
  | .Init_float32 n => txt (float32F n 15)
  | .Init_float64 n => txt (floatF n 15)
  | .Init_space n => txt s!"/* skip {n} */" ++ ppf "@ "
  | .Init_addrof symb ofs =>
    if wrapSigned 32 (CamlNum.toZ ofs) == 0 then txt s!"&{externAtom symb}"
    else txt s!"(void *)((char *)&{externAtom symb} + {ci32 ofs})"

/-- `PrintCsyntax.print_composite_init` -/
def printCompositeInit (il : List InitData) : Doc :=
  ppf "{@ " ++
  (il.foldl (fun d i => d ++ printInit i ++
    (match i with | .Init_space _ => #[] | _ => ppf ",@ ")) #[]) ++
  txt "}"

/-- `PrintCsyntax.print_globvar` -/
def printGlobvar (info : AtomInfo) (id : Ident) (v : GlobVar Ty) : Doc :=
  let name1 := externAtom id
  let name2 := if v.gvar_readonly then "const " ++ name1 else name1
  match v.gvar_init with
  | [] => txt s!"extern {nameCdecl name2 v.gvar_info};" ++ ppf "@ @ "
  | [.Init_space _] => txt s!"{nameCdecl name2 v.gvar_info};" ++ ppf "@ @ "
  | il =>
    ppf "@[<hov 2>" ++ txt s!"{nameCdecl name2 v.gvar_info} = " ++
    (match v.gvar_info, il with
     | .Tint .., [i1] | .Tlong .., [i1] | .Tfloat .., [i1] | .Tpointer .., [i1]
     | .Tfunction .., [i1] => printInit i1
     | _, il =>
       if info.isStringLiteral id then txt s!"\"{stringOfInit (chopLastNul il)}\""
       else printCompositeInit il) ++
    ppf ";@]@ @ "

/-- `PrintCsyntax.print_globvardecl` -/
def printGlobvardecl (info : AtomInfo) (id : Ident) (v : GlobVar Ty) : Doc :=
  let name := externAtom id
  let name := if v.gvar_readonly then "const " ++ name else name
  let linkage := if info.isStatic id then "static" else "extern"
  txt s!"{linkage} {nameCdecl name v.gvar_info};" ++ ppf "@ @ "

/-- `PrintCsyntax.print_globdecl` -/
def printGlobdecl (info : AtomInfo) : Ident × GlobDef Csyntax.FunDef Ty → Doc
  | (id, .Gfun f) => printFundecl info id f
  | (id, .Gvar v) => printGlobvardecl info id v

/-- `PrintCsyntax.print_globdef` -/
def printGlobdef (info : AtomInfo) : Ident × GlobDef Csyntax.FunDef Ty → Doc
  | (id, .Gfun f) => printFundef id f
  | (id, .Gvar v) => printGlobvar info id v

/-- `PrintCsyntax.struct_or_union` -/
def structOrUnion : SU → String
  | .Struct => "struct"
  | .Union => "union"

/-- `PrintCsyntax.declare_composite` -/
def declareComposite : CompositeDef → Doc
  | .Composite id su _ _ => txt s!"{structOrUnion su} {externAtom id};" ++ ppf "@ "

/-- `PrintCsyntax.print_member` -/
def printMember : Member → Doc
  | .Member_plain id ty => ppf "@ " ++ txt s!"{nameCdecl (externAtom id) ty};"
  | .Member_bitfield id sz sg attr w _ =>
    ppf "@ " ++ txt s!"{nameCdecl (externAtom id) (.Tint sz sg attr)} : {w};"

/-- `PrintCsyntax.define_composite` -/
def defineComposite : CompositeDef → Doc
  | .Composite id su m a =>
    ppf "@[<v 2>" ++ txt s!"{structOrUnion su} {externAtom id}{attributes a} \{" ++
    (m.foldl (fun d mb => d ++ printMember mb) #[]) ++
    ppf "@;<0 -2>};@]@ @ "

/-- `PrintCsyntax.print_program`, as a document. -/
def programDoc (info : AtomInfo) (prog : Csyntax.Program) : Doc :=
  ppf "@[<v 0>" ++
  (prog.prog_types.foldl (fun d c => d ++ declareComposite c) #[]) ++
  (prog.prog_types.foldl (fun d c => d ++ defineComposite c) #[]) ++
  (prog.prog_defs.foldl (fun d g => d ++ printGlobdecl info g) #[]) ++
  (prog.prog_defs.foldl (fun d g => d ++ printGlobdef info g) #[]) ++
  ppf "@]@."

/-- `PrintCsyntax.print_program` -/
def printProgram (prog : Csyntax.Program) (info : AtomInfo := {}) : String :=
  render (programDoc info prog)

/-- `PrintCsyntax.print_if` -/
def printIf (destination : Option String) (prog : Csyntax.Program) (info : AtomInfo := {}) :
    IO Unit :=
  match destination with
  | none => pure ()
  | some f => IO.FS.writeFile f (printProgram prog info)

#guard nameType (.Tpointer (.Tfunction [.Tint .I32 .Signed noattr] .Tvoid cc_default) noattr) =
  "void (*)(int)"
#guard nameCdecl "a" (.Tarray (.Tpointer (.Tint .I8 .Signed noattr) noattr) 3 noattr) =
  "signed char *a[3]"
#guard nameCdecl "f" (.Tfunction [] (.Tlong .Unsigned noattr) cc_default) =
  "unsigned long long f(void)"

end PrintCsyntax
end CC
