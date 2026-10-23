/-
  Port of `cparser/Cprint.ml`: pretty-printer for the C abstract syntax of
  `cparser/C.lean`.

  The OCaml printers write to a `Format` formatter; here they return a
  `Format.Doc` (see `lib/Format.lean`), rendered by `Format.render`.  The
  global flags `print_idents_in_full`, `print_debug_idents` and
  `print_line_numbers` are the fields of `Cprint.Opts`.  `print_if` (which
  writes to the file named by `-dc`) is `print_if`, returning the text.
-/
import CCLib.cparser.C
import CCLib.lib.Format

namespace CC
namespace CParser
namespace Cprint

open C Format

structure Opts where
  print_idents_in_full : Bool := false
  print_debug_idents : Bool := false
  print_line_numbers : Bool := false
  deriving Inhabited

variable (o : Opts)
include o

omit o in
/-- Lower-case hexadecimal digits of a natural number. -/
def hexDigits (n : Nat) : String := String.ofList (Nat.toDigits 16 n)

omit o in
/-- Pad on the left with `c` to width `w`. -/
def padLeft (s : String) (w : Nat) (c : Char := '0') : String :=
  String.ofList (List.replicate (w - s.length) c) ++ s

def location (loc : Location) : Doc :=
  let (file, lineno) := loc
  if o.print_line_numbers && lineno ≥ 0 then
    txt s!"# {lineno} \"{file}\"" ++ ppf "@ "
  else #[]

def ident (i : Ident) : Doc :=
  if o.print_debug_idents then txt s!"${i.stamp}"
  else if o.print_idents_in_full then txt s!"{i.name}${i.stamp}"
  else txt i.name

omit o in
/-- The characters of a string literal (`CStr`), escaped. -/
def quoteString (s : String) : String := Id.run do
  let mut r := "\""
  for c in s.toList do
    let n := c.toNat
    if n == 9 then r := r ++ "\\t"
    else if n == 10 then r := r ++ "\\n"
    else if n == 13 then r := r ++ "\\r"
    else if c == '"' then r := r ++ "\\\""
    else if c == '\\' then r := r ++ "\\\\"
    else if c ≥ ' ' && c ≤ '~' then r := r.push c
    else r := r ++ "\\" ++ padLeft (String.ofList (Nat.toDigits 8 (n % 256))) 3
  return r ++ "\""

def const : Constant → Doc
  | .CInt v ik s =>
      if s != "" then txt s
      else
        txt (toString v.toInt) ++
        (match ik with
         | .IULongLong => txt "ULL"
         | .ILongLong => txt "LL"
         | .IULong => txt "UL"
         | .ILong => txt "L"
         | .IUInt => txt "U"
         | _ => #[])
  | .CFloat v fk =>
      (if v.hex then txt s!"0x{v.intPart}.{v.fracPart}P{v.exp}"
       else txt s!"{v.intPart}.{v.fracPart}E{v.exp}") ++
      (match fk with
       | .FFloat16 => #[]
       | .FFloat => txt "F"
       | .FLongDouble => txt "L"
       | .FDouble => #[])
  | .CStr s => txt (quoteString s)
  | .CWStr l _ =>
      let body := l.foldl (fun acc c =>
        if c ≥ 32 && c ≤ 126 && c != 34 && c != 92 then
          acc.push (Char.ofNat c.toInt.toNat)
        else acc ++ "\" \"\\x" ++ padLeft (hexDigits c.toUInt64.toNat) 2 ++ "\" \"") ""
      txt ("L\"" ++ body ++ "\"")
  | .CEnum id _ => ident o id

def attr_arg : AttrArg → Doc
  | .AIdent s => txt s
  | .AInt n => txt (toString n.toInt)
  | .AString s => const o (.CStr s)

def «attribute» : Attribute → Doc
  | .AConst => txt "const"
  | .AVolatile => txt "volatile"
  | .ARestrict => txt "restrict"
  | .AAlignas n => txt s!"_Alignas({n})"
  | .Attr name [] => txt s!"__attribute__(({name}))"
  | .Attr name (arg1 :: args) =>
      txt s!"__attribute__(({name}(" ++ attr_arg o arg1 ++
      args.foldl (fun d aa => d ++ txt ", " ++ attr_arg o aa) #[] ++ txt ")))"

def attributes (al : Attributes) : Doc :=
  al.foldl (fun d a => d ++ txt " " ++ «attribute» o a) #[]

omit o in
def name_of_ikind : IKind → String
  | .IBool => "_Bool"
  | .IChar => "char"
  | .ISChar => "signed char"
  | .IUChar => "unsigned char"
  | .IInt => "int"
  | .IUInt => "unsigned int"
  | .IShort => "short"
  | .IUShort => "unsigned short"
  | .ILong => "long"
  | .IULong => "unsigned long"
  | .ILongLong => "long long"
  | .IULongLong => "unsigned long long"

omit o in
def name_of_fkind : FKind → String
  | .FFloat16 => "_Float16"
  | .FFloat => "float"
  | .FDouble => "double"
  | .FLongDouble => "long double"

/-- `dcl ~pp_indication pp ty n`: print declarator of type `ty` around the
    name printed by `n`. -/
partial def dcl (pp_indication : Bool := true) (ty : Typ) (n : Doc) : Doc :=
  match ty with
  | .TVoid a => txt "void" ++ attributes o a ++ n
  | .TInt k a => txt (name_of_ikind k) ++ attributes o a ++ n
  | .TFloat k a => txt (name_of_fkind k) ++ attributes o a ++ n
  | .TPtr t a =>
      let n' := match t with
        | .TFun .. | .TArray .. => txt " (*" ++ attributes o a ++ n ++ txt ")"
        | _ => txt " *" ++ attributes o a ++ n
      dcl pp_indication t n'
  | .TArray t sz a =>
      let n' := n ++
        (match a with
         | [] => txt "["
         | _ => txt "[" ++ attributes o a ++ txt " ") ++
        (match sz with
         | none => txt "]"
         | some i => txt s!"{i.toInt}]")
      dcl pp_indication t n'
  | .TFun tres args vararg a =>
      let param : Ident × Typ → Doc := fun (id, ty) =>
        dcl pp_indication ty (txt " " ++ ident o id)
      let n' := attributes o a ++ n ++ txt "(" ++
        (if pp_indication then ppf "@[<hov 0>" else #[]) ++
        (match args with
         | none => #[]
         | some [] => if vararg then txt "..." else txt "void"
         | some (a1 :: al) =>
            param a1 ++
            al.foldl (fun d a =>
              d ++ (if pp_indication then ppf ",@ " else txt ", ") ++ param a) #[] ++
            (if vararg then txt ", ..." else #[])) ++
        (if pp_indication then ppf "@]" else #[]) ++ txt ")"
      dcl pp_indication tres n'
  | .TNamed id a => ident o id ++ attributes o a ++ n
  | .TStruct id a => txt "struct " ++ ident o id ++ attributes o a ++ n
  | .TUnion id a => txt "union " ++ ident o id ++ attributes o a ++ n
  | .TEnum id a => txt "enum " ++ ident o id ++ attributes o a ++ n

def typ (ty : Typ) : Doc := dcl o true ty #[]

def typ_raw (ty : Typ) : Doc := dcl o false ty #[]

omit o in
inductive Associativity where
  | LtoR | RtoL | NA
  deriving BEq, DecidableEq

omit o in
open BinaryOperator UnaryOperator in
/-- H&S section 7.2 -/
def precedence : ExpDesc → Int × Associativity
  | .EConst _ => (16, .NA)
  | .ESizeof _ => (15, .RtoL)
  | .EAlignof _ => (15, .RtoL)
  | .EVar _ => (16, .NA)
  | .EBinop Oindex _ _ _ => (16, .LtoR)
  | .ECall _ _ => (16, .LtoR)
  | .EUnop (Odot _) _ | .EUnop (Oarrow _) _ => (16, .LtoR)
  | .EUnop Opostincr _ | .EUnop Opostdecr _ => (16, .LtoR)
  | .EUnop _ _ => (15, .RtoL)
  | .ECast _ _ | .ECompound _ _ => (14, .RtoL)
  | .EBinop op _ _ _ =>
    match op with
    | Omul | Odiv | Omod => (13, .LtoR)
    | Oadd | Osub => (12, .LtoR)
    | Oshl | Oshr => (11, .LtoR)
    | Olt | Ogt | Ole | Oge => (10, .LtoR)
    | Oeq | BinaryOperator.One => (9, .LtoR)
    | Oand => (8, .LtoR)
    | Oxor => (7, .LtoR)
    | Oor => (6, .LtoR)
    | Ologand => (5, .LtoR)
    | Ologor => (4, .LtoR)
    | Oassign | Oadd_assign | Osub_assign | Omul_assign | Odiv_assign
    | Omod_assign | Oand_assign | Oor_assign | Oxor_assign | Oshl_assign
    | Oshr_assign => (2, .RtoL)
    | Ocomma => (1, .LtoR)
    | Oindex => (16, .LtoR)
  | .EConditional _ _ _ => (3, .RtoL)

omit o in
open BinaryOperator in
/-- The text of a binary operator and whether the break hint comes before
    (`a@ + b`) or after it (`a =@ b`). -/
def binopText : BinaryOperator → String × Bool
  | Oadd => ("+", true) | Osub => ("-", true) | Omul => ("*", true)
  | Odiv => ("/", true) | Omod => ("%", true) | Oand => ("&", true)
  | Oor => ("|", true) | Oxor => ("^", true) | Oshl => ("<<", true)
  | Oshr => (">>", true) | Oeq => ("==", true) | BinaryOperator.One => ("!=", true)
  | Olt => ("<", true) | Ogt => (">", true) | Ole => ("<=", true)
  | Oge => (">=", true) | Ologand => ("&&", true) | Ologor => ("||", true)
  | Oassign => ("=", false) | Oadd_assign => ("+=", false)
  | Osub_assign => ("-=", false) | Omul_assign => ("*=", false)
  | Odiv_assign => ("/=", false) | Omod_assign => ("%=", false)
  | Oand_assign => ("&=", false) | Oor_assign => ("|=", false)
  | Oxor_assign => ("^=", false) | Oshl_assign => ("<<=", false)
  | Oshr_assign => (">>=", false)
  | Ocomma => (",", false) | Oindex => ("[]", false)

mutual
partial def exp (prec : Int) (a : Exp) : Doc :=
  let (prec', assoc) := precedence a.edesc
  let (prec1, prec2) := if assoc == .LtoR then (prec', prec' + 1) else (prec' + 1, prec')
  let opening := if prec' < prec then ppf "@[<hov 2>(" else ppf "@[<hov 2>"
  let body : Doc := match a.edesc with
    | .EConst cst => const o cst
    | .EVar id => ident o id
    | .ESizeof ty => txt "sizeof(" ++ typ o ty ++ txt ")"
    | .EAlignof ty => txt "__alignof(" ++ typ o ty ++ txt ")"
    | .EUnop .Ominus a1 => txt "-" ++ exp prec' a1
    | .EUnop .Oplus a1 => txt "+" ++ exp prec' a1
    | .EUnop .Olognot a1 => txt "!" ++ exp prec' a1
    | .EUnop .Onot a1 => txt "~" ++ exp prec' a1
    | .EUnop .Oderef a1 => txt "*" ++ exp prec' a1
    | .EUnop .Oaddrof a1 => txt "&" ++ exp prec' a1
    | .EUnop .Opreincr a1 => txt "++" ++ exp prec' a1
    | .EUnop .Opredecr a1 => txt "--" ++ exp prec' a1
    | .EUnop .Opostincr a1 => exp prec' a1 ++ txt "++"
    | .EUnop .Opostdecr a1 => exp prec' a1 ++ txt "--"
    | .EUnop (.Odot s) a1 => exp prec' a1 ++ txt ("." ++ s)
    | .EUnop (.Oarrow s) a1 => exp prec' a1 ++ txt ("->" ++ s)
    | .EBinop .Oindex a1 a2 _ => exp prec1 a1 ++ txt "[" ++ exp 0 a2 ++ txt "]"
    | .EBinop op a1 a2 _ =>
        let (s, before) := binopText op
        if before then exp prec1 a1 ++ ppf "@ " ++ txt (s ++ " ") ++ exp prec2 a2
        else if op == .Ocomma then exp prec1 a1 ++ txt "," ++ ppf "@ " ++ exp prec2 a2
        else exp prec1 a1 ++ txt (" " ++ s) ++ ppf "@ " ++ exp prec2 a2
    | .EConditional a1 a2 a3 =>
        exp 4 a1 ++ ppf "@ ? " ++ exp 4 a2 ++ ppf "@ : " ++ exp 4 a3
    | .ECast ty a1 => txt "(" ++ typ o ty ++ txt ") " ++ exp prec' a1
    | .ECompound ty i => txt "(" ++ typ o ty ++ txt ") " ++ init i
    | .ECall (.mk (.EVar { name := "__builtin_va_start", .. }) _)
        [a1, .mk (.EUnop .Oaddrof a2) _] =>
        txt "__builtin_va_start" ++ ppf "@[<hov 1>(" ++ exp 2 a1 ++ ppf ",@ " ++
          exp 2 a2 ++ ppf ")@]"
    | .ECall (.mk (.EVar { name := "__builtin_va_arg", .. }) _)
        [a1, .mk (.ESizeof ty) _] =>
        txt "__builtin_va_arg" ++ ppf "@[<hov 1>(" ++ exp 2 a1 ++ ppf ",@ " ++
          typ o ty ++ ppf ")@]"
    | .ECall a1 al =>
        exp prec' a1 ++ ppf "@[<hov 1>(" ++
        (match al with
         | [] => #[]
         | a1 :: al => exp 2 a1 ++ al.foldl (fun d a => d ++ ppf ",@ " ++ exp 2 a) #[]) ++
        ppf ")@]"
  opening ++ body ++ (if prec' < prec then ppf ")@]" else ppf "@]")

partial def init : Init → Doc
  | .Init_single e => exp 2 e
  | .Init_array il =>
      ppf "@[<hov 1>{" ++ il.foldl (fun d i => d ++ init i ++ ppf ",@ ") #[] ++ ppf "}@]"
  | .Init_struct _ il =>
      ppf "@[<hov 1>{" ++ il.foldl (fun d (_, i) => d ++ init i ++ ppf ",@ ") #[] ++
        ppf "}@]"
  | .Init_union _ fld i =>
      ppf "@[<hov 2>{." ++ txt fld.fld_name ++ ppf " =@ " ++ init i ++ ppf "}@]"
end

def simple_decl (id : Ident) (ty : Typ) : Doc :=
  dcl o true ty (txt " " ++ ident o id)

def storage : Storage → Doc
  | .Storage_default => #[]
  | .Storage_extern => txt "extern "
  | .Storage_static => txt "static "
  | .Storage_auto => #[]
  | .Storage_register => txt "register "

def full_decl : Decl → Doc
  | .mk sto id ty int =>
      ppf "@[<hov 2>" ++ storage sto ++ dcl o true ty (txt " " ++ ident o id) ++
      (match int with
       | none => #[]
       | some i => ppf " =@ " ++ init o i) ++
      ppf ";@]"

def asm_operand : AsmOperand → Doc
  | (label, constr, e) =>
      (match label with
       | none => #[]
       | some l => txt s!"[{l}] ") ++
      const o (.CStr constr) ++ txt " (" ++ exp o 0 e ++ txt ")"

def asm_operands : List AsmOperand → Doc
  | [] => #[]
  | op1 :: ops =>
      ppf "@[<hov 0>" ++ asm_operand o op1 ++
      ops.foldl (fun d op => d ++ ppf ",@ " ++ asm_operand o op) #[] ++ ppf "@]"

def asm_flags : List String → Doc
  | [] => #[]
  | fl1 :: fls =>
      ppf "@[<hov 0>" ++ const o (.CStr fl1) ++
      fls.foldl (fun d fl => d ++ ppf ",@ " ++ const o (.CStr fl)) #[] ++ ppf "@]"

omit o in
/-- `exp_of_stmt`; `none` for the exception `Not_expr`. -/
partial def exp_of_stmt (s : Stmt) : Option Exp :=
  match s.sdesc with
  | .Sdo e => some e
  | .Sseq s1 s2 => do
      let e1 ← exp_of_stmt s1
      let e2 ← exp_of_stmt s2
      return .mk (.EBinop .Ocomma e1 e2 (.TVoid [])) (.TVoid [])
  | .Sif e s1 s2 => do
      let e1 ← exp_of_stmt s1
      let e2 ← exp_of_stmt s2
      return .mk (.EConditional e e1 e2) (.TVoid [])
  | _ => none

omit o in
private def isSkip (s : Stmt) : Bool := match s.sdesc with | .Sskip => true | _ => false

mutual
partial def stmt (s : Stmt) : Doc :=
  location o s.sloc ++
  match s.sdesc with
  | .Sskip => txt "/*skip*/;"
  | .Sdo e => exp o 0 e ++ txt ";"
  | .Sseq s1 s2 => stmt s1 ++ ppf "@ " ++ stmt s2
  | .Sif e s1 s2 =>
      if isSkip s2 then
        ppf "@[<v 2>if (" ++ exp o 0 e ++ ppf ") {@ " ++ stmt_block s1 ++ ppf "@;<0 -2>}@]"
      else if isSkip s1 then
        let not_e := Exp.mk (.EUnop .Olognot e) (.TInt .IInt [])
        ppf "@[<v 2>if (" ++ exp o 0 not_e ++ ppf ") {@ " ++ stmt_block s2 ++
          ppf "@;<0 -2>}@]"
      else
        ppf "@[<v 2>if (" ++ exp o 0 e ++ ppf ") {@ " ++ stmt_block s1 ++
          ppf "@;<0 -2>} else {@ " ++ stmt_block s2 ++ ppf "@;<0 -2>}@]"
  | .Swhile e s1 =>
      ppf "@[<v 2>while (" ++ exp o 0 e ++ ppf ") {@ " ++ stmt_block s1 ++ ppf "@;<0 -2>}@]"
  | .Sdowhile s1 e =>
      ppf "@[<v 2>do {@ " ++ stmt_block s1 ++ ppf "@;<0 -2>} while(" ++ exp o 0 e ++
        ppf ");@]"
  | .Sfor e1 e2 e3 s1 =>
      ppf "@[<v 2>for (@[<hv 0>" ++ opt_exp e1 ++ ppf ";@ " ++ exp o 0 e2 ++ ppf ";@ " ++
        opt_exp e3 ++ ppf ") {@]@ " ++ stmt_block s1 ++ ppf "@;<0 -2>}@]"
  | .Sbreak => txt "break;"
  | .Scontinue => txt "continue;"
  | .Sswitch e s1 =>
      ppf "@[<v 2>switch (" ++ exp o 0 e ++ ppf ") {@ " ++ stmt_block s1 ++
        ppf "@;<0 -2>}@]"
  | .Slabeled lbl s1 => slabel lbl ++ ppf ":@ " ++ stmt s1
  | .Sgoto lbl => txt s!"goto {lbl};"
  | .Sreturn none => txt "return;"
  | .Sreturn (some e) => txt "return " ++ exp o 0 e ++ txt ";"
  | .Sblock _ => ppf "@[<v 2>{@ " ++ stmt_block s ++ ppf "@;<0 -2>}@]"
  | .Sdecl d => full_decl o d
  | .Sasm attrs txt' [] [] [] =>
      txt "asm" ++ attributes o attrs ++ txt "(" ++ const o (.CStr txt') ++ txt ");"
  | .Sasm attrs txt' outputs inputs [] =>
      txt "asm" ++ attributes o attrs ++ ppf "(@[<hov 0>" ++ const o (.CStr txt') ++
        ppf "@ :" ++ asm_operands o outputs ++ ppf "@ :" ++ asm_operands o inputs ++
        ppf "@]);"
  | .Sasm attrs txt' outputs inputs flags =>
      txt "asm" ++ attributes o attrs ++ ppf "(@[<hov 0>" ++ const o (.CStr txt') ++
        ppf "@ :" ++ asm_operands o outputs ++ ppf "@ :" ++ asm_operands o inputs ++
        ppf "@ : " ++ asm_flags o flags ++ ppf "@]);"

partial def slabel : SLabel → Doc
  | .Slabel s => txt s
  | .Scase e _ => txt "case " ++ exp o 0 e
  | .Sdefault => txt "default"

partial def stmt_block (s : Stmt) : Doc :=
  match s.sdesc with
  | .Sblock [] => #[]
  | .Sblock (s1 :: sl) => stmt s1 ++ sl.foldl (fun d s => d ++ ppf "@ " ++ stmt s) #[]
  | _ => stmt s

partial def opt_exp (s : Stmt) : Doc :=
  if isSkip s then txt "/*nothing*/" else
  match exp_of_stmt s with
  | some e => exp o 0 e
  | none => ppf "@[<v 3>({ " ++ stmt s ++ ppf " })@]"
end

def fundef (f : Fundef) : Doc :=
  ppf "@[<hov 2>" ++ txt (if f.fd_inline then "inline " else "") ++ storage f.fd_storage ++
  simple_decl o f.fd_name (.TFun f.fd_ret (some f.fd_params) f.fd_vararg f.fd_attrib) ++
  ppf "@]@ @[<v 2>{@ " ++
  f.fd_locals.foldl (fun d dl => d ++ full_decl o dl ++ ppf "@ ") #[] ++
  stmt_block o f.fd_body ++
  ppf "@;<0 -2>}@]@ @ "

def field (f : Field) : Doc :=
  simple_decl o { name := f.fld_name, stamp := 0 } f.fld_typ ++
  match f.fld_bitfield with
  | none => #[]
  | some n => txt s!" : {n}"

omit o in
private def suName : StructOrUnion → String
  | .Struct => "struct"
  | .Union => "union"

def globdecl (g : Globdecl) : Doc :=
  location o g.gloc ++
  match g.gdesc with
  | .Gdecl d => full_decl o d ++ ppf "@ @ "
  | .Gfundef f => fundef o f
  | .Gcompositedecl kind id attrs =>
      txt (suName kind) ++ attributes o attrs ++ txt " " ++ ident o id ++ ppf ";@ @ "
  | .Gcompositedef kind id attrs flds =>
      ppf "@[<v 2>" ++ txt (suName kind) ++ attributes o attrs ++ txt " " ++ ident o id ++
        txt " {" ++ flds.foldl (fun d fld => d ++ ppf "@ " ++ field o fld ++ txt ";") #[] ++
        ppf "@;<0 -2>};@]@ @ "
  | .Gtypedef id ty =>
      ppf "@[<hov 2>typedef " ++ simple_decl o id ty ++ ppf ";@]@ @ "
  | .Genumdef id attrs vals =>
      ppf "@[<v 2>enum" ++ attributes o attrs ++ txt " " ++ ident o id ++ txt " {" ++
        vals.foldl (fun d (name, _, opt_e) =>
          d ++ ppf "@ " ++ ident o name ++
          (match opt_e with
           | none => #[]
           | some e => txt " = " ++ exp o 0 e) ++ txt ",") #[] ++
        ppf "@;<0 -2>};@]@ @ "
  | .Gpragma s => txt s!"#pragma {s}" ++ ppf "@ @ "

def program (prog : Program) : Doc :=
  ppf "@[<v 0>" ++ prog.foldl (fun d g => d ++ globdecl o g) #[] ++ ppf "@]@."

omit o in
/-- Render a document produced by this printer. -/
def toText (d : Doc) : String := Format.render d

/-- `print_if`: the text that `-dc` writes, if a destination is given. -/
def print_if (destination : Option String) (prog : Program) : Option (String × String) :=
  destination.map fun f => (f, toText (program o prog))

end Cprint
end CParser
end CC
