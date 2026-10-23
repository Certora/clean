/-
  Instruction selection (Cminor → CminorSel) for RV64 — port of
  `backend/Selection.v` instantiated with the RISC-V operators
  (`CCLib/riscV/SelectOp.lean`, `CCLib/riscV/SelectLong.lean`,
  `CCLib/riscV/SelectDiv.lean`).  In this port `CCLib/backend/Selection.lean`
  is the aarch64 instance and `CCLib/x86/Selection.lean` the x86-64 one.

  Ported (RISC-V instance): `condexpr_of_expr`, `condition_of_expr`, `load`,
  `store`, `sel_constant`, `sel_unop`, `sel_binop`, `sel_select`,
  `sel_expr`, `sel_exprlist`, `sel_select_expr`, `sel_builtin_arg(s)`,
  `sel_known_builtin`, `Sno_op`, `sel_builtin_default`, `sel_builtin`,
  `sel_switch`, `sel_switch_int`, `sel_switch_long`, `if_conversion_base`,
  `if_conversion`, `sel_stmt`, `sel_function`, `sel_fundef`, `sel_program`.

  The definitions of `Selection.v` that only mention Cminor — `globdef`,
  `call_kind`, `expr_is_addrof_ident`, `classify_call`, `sel_builtin_res`,
  `stmt_class`, `classify_stmt`, `known_id`, `globdef_of_interest`,
  `record_globdefs`, `lookup_helper_aux`, `lookup_helper`, `get_helpers` —
  are shared with `CCLib/backend/Selection.lean`.

  As on aarch64, the section variable `hf : helper_functions` is not used by
  the selection functions themselves: on RV64 every 64-bit operation,
  including the unsigned conversions, is native.  `sel_switch_long` uses
  `SplitLong.lowlong` (`CCLib/riscV/SplitLong.lean`).

  Differences from Rocq: the OCaml parameters of the pass
  (`SelectOp.symbol_is_relocatable`, `Compopts.optim_for_size`,
  `Selection.compile_switch`, `Selection.if_conversion_heuristic`) are the
  fields of an explicit `Options` argument; error messages are plain strings.
-/
import CCLib.backend.Selection
import CCLib.riscV.SelectDiv
import CCLib.riscV.SplitLong
import CCLib.riscV.CminorSel

namespace CC
namespace RiscV
namespace Selection

open Op CminorSel SelectOp SelectLong SelectDiv SplitLong Cminortyping Builtins
open CC.SplitLong (HelperFunctions)
open CC.Selection (Globdef CallKind exprIsAddrofIdent classifyCall selBuiltinRes StmtClass
  classifyStmt getHelpers)

/-- CminorSel expressions (RISC-V). -/
abbrev Expr := CminorSel.Expr
/-- CminorSel expression lists (RISC-V). -/
abbrev Exprlist := CminorSel.Exprlist
/-- CminorSel statements (RISC-V). -/
abbrev Stmt := CminorSel.Stmt

open CminorSel.Expr CminorSel.Exprlist CminorSel.Condexpr CminorSel.Exitexpr CminorSel.Stmt

local infixr:67 " ::: " => CminorSel.Exprlist.Econs

/-- The OCaml parameters of instruction selection. -/
structure Options where
  /-- `SelectOp.symbol_is_relocatable` -/
  symbolIsRelocatable : Ident → Bool := fun _ => false
  /-- `Compopts.optim_for_size` -/
  optimForSize : Bool := false
  /-- `Selection.compile_switch` (the untrusted switch compiler; validated). -/
  compileSwitch : Z → Nat → Switch.Table → Switch.Comptree
  /-- `Selection.if_conversion_heuristic` -/
  ifConversionHeuristic : Ident → Cminor.Expr → Cminor.Expr → Cminor.Expr → ATyp → Stmt → Bool :=
    fun _ _ _ _ _ _ => true

/-! ## Conversion of conditions -/

/-- `Selection.condexpr_of_expr` -/
def condexprOfExpr : Expr → Condexpr
  | Eop (.Ocmp c) el => CEcond c el
  | Econdition a b c => CEcondition a (condexprOfExpr b) (condexprOfExpr c)
  | Elet a b => CElet a (condexprOfExpr b)
  | e => CEcond (.Ccompuimm .Cne Integers.Int.zero) (e ::: Enil)

/-- `Selection.condition_of_expr` -/
def conditionOfExpr (e : Expr) : Condition × Exprlist :=
  match e with
  | Eop (.Ocmp c) el => (c, el)
  | _ => (.Ccompuimm .Cne Integers.Int.zero, e ::: Enil)

section SELECTION
variable (opts : Options)

/-- `Selection.load` -/
def load (chunk : Chunk) (e1 : Expr) : Expr :=
  match addressing opts.symbolIsRelocatable chunk e1 with
  | (mode, args) => Eload chunk mode args

/-- `Selection.store` -/
def store (chunk : Chunk) (e1 e2 : Expr) : Stmt :=
  match addressing opts.symbolIsRelocatable chunk e1 with
  | (mode, args) => Sstore chunk mode args e2

/-- `Selection.sel_constant` -/
def selConstant (cst : Cminor.Constant) : Expr :=
  match cst with
  | .Ointconst n => Eop (.Ointconst n) Enil
  | .Ofloatconst f => Eop (.Ofloatconst f) Enil
  | .Osingleconst f => Eop (.Osingleconst f) Enil
  | .Olongconst n => longconst n
  | .Oaddrsymbol id ofs => addrsymbol id ofs
  | .Oaddrstack ofs => addrstack ofs

/-- `Selection.sel_unop` -/
def selUnop (op : Cminor.UnaryOperation) (arg : Expr) : Expr :=
  match op with
  | .Ocast8unsigned => cast8unsigned arg
  | .Ocast8signed => cast8signed arg
  | .Ocast16unsigned => cast16unsigned arg
  | .Ocast16signed => cast16signed arg
  | .Onegint => negint arg
  | .Onotint => notint arg
  | .Onegf => negf arg
  | .Oabsf => absf arg
  | .Onegfs => negfs arg
  | .Oabsfs => absfs arg
  | .Osingleoffloat => singleoffloat arg
  | .Ofloatofsingle => floatofsingle arg
  | .Ointoffloat => intoffloat arg
  | .Ointuoffloat => intuoffloat arg
  | .Ofloatofint => floatofint arg
  | .Ofloatofintu => floatofintu arg
  | .Ointofsingle => intofsingle arg
  | .Ointuofsingle => intuofsingle arg
  | .Osingleofint => singleofint arg
  | .Osingleofintu => singleofintu arg
  | .Onegl => negl arg
  | .Onotl => notl arg
  | .Ointoflong => intoflong arg
  | .Olongofint => longofint arg
  | .Olongofintu => longofintu arg
  | .Olongoffloat => longoffloat arg
  | .Olonguoffloat => longuoffloat arg
  | .Ofloatoflong => floatoflong arg
  | .Ofloatoflongu => floatoflongu arg
  | .Olongofsingle => longofsingle arg
  | .Olonguofsingle => longuofsingle arg
  | .Osingleoflong => singleoflong arg
  | .Osingleoflongu => singleoflongu arg

/-- `Selection.sel_binop` -/
def selBinop (op : Cminor.BinaryOperation) (arg1 arg2 : Expr) : Expr :=
  match op with
  | .Oadd => add arg1 arg2
  | .Osub => sub arg1 arg2
  | .Omul => mul arg1 arg2
  | .Odiv => divs opts.optimForSize arg1 arg2
  | .Odivu => divu opts.optimForSize arg1 arg2
  | .Omod => mods opts.optimForSize arg1 arg2
  | .Omodu => modu opts.optimForSize arg1 arg2
  | .Oand => and arg1 arg2
  | .Oor => or arg1 arg2
  | .Oxor => xor arg1 arg2
  | .Oshl => shl arg1 arg2
  | .Oshr => shr arg1 arg2
  | .Oshru => shru arg1 arg2
  | .Oaddf => addf arg1 arg2
  | .Osubf => subf arg1 arg2
  | .Omulf => mulf arg1 arg2
  | .Odivf => divf arg1 arg2
  | .Oaddfs => addfs arg1 arg2
  | .Osubfs => subfs arg1 arg2
  | .Omulfs => mulfs arg1 arg2
  | .Odivfs => divfs arg1 arg2
  | .Oaddl => addl arg1 arg2
  | .Osubl => subl arg1 arg2
  | .Omull => mull arg1 arg2
  | .Odivl => divls opts.optimForSize arg1 arg2
  | .Odivlu => divlu opts.optimForSize arg1 arg2
  | .Omodl => modls opts.optimForSize arg1 arg2
  | .Omodlu => modlu opts.optimForSize arg1 arg2
  | .Oandl => andl arg1 arg2
  | .Oorl => orl arg1 arg2
  | .Oxorl => xorl arg1 arg2
  | .Oshll => shll arg1 arg2
  | .Oshrl => shrl arg1 arg2
  | .Oshrlu => shrlu arg1 arg2
  | .Ocmp c => comp c arg1 arg2
  | .Ocmpu c => compu c arg1 arg2
  | .Ocmpf c => compf c arg1 arg2
  | .Ocmpfs c => compfs c arg1 arg2
  | .Ocmpl c => cmpl c arg1 arg2
  | .Ocmplu c => cmplu c arg1 arg2

/-- `Selection.sel_select` -/
def selSelect (ty : ATyp) (cnd ifso ifnot : Expr) : Expr :=
  let (cond, args) := conditionOfExpr cnd
  if selectSupported ty then select ty cond args ifso ifnot
  else Econdition (condexprOfExpr cnd) ifso ifnot

/-- `Selection.sel_expr` -/
def selExpr : Cminor.Expr → Expr
  | .Evar id => Evar id
  | .Econst cst => selConstant cst
  | .Eunop op arg => selUnop op (selExpr arg)
  | .Ebinop op arg1 arg2 => selBinop opts op (selExpr arg1) (selExpr arg2)
  | .Eload chunk addr => load opts chunk (selExpr addr)

/-- `Selection.sel_exprlist` -/
def selExprlist : List Cminor.Expr → Exprlist
  | [] => Enil
  | a :: bl => Econs (selExpr opts a) (selExprlist bl)

/-- `Selection.sel_select_expr` -/
def selSelectExpr (ty : ATyp) (arg1 arg2 arg3 : Cminor.Expr) : Expr :=
  let (cond, args) := conditionOfExpr (selExpr opts arg1)
  select ty cond args (selExpr opts arg2) (selExpr opts arg3)

/-- `Selection.sel_builtin_arg` -/
def selBuiltinArg (e : Cminor.Expr) (c : BuiltinArgConstraint) : BuiltinArg Expr :=
  let e' := selExpr opts e
  let ba := builtinArg e'
  if builtinArgOk ba c then ba else .BA e'

/-- `Selection.sel_builtin_args` -/
def selBuiltinArgs : List Cminor.Expr → List BuiltinArgConstraint → List (BuiltinArg Expr)
  | [], _ => []
  | e :: el, cl => selBuiltinArg opts e (cl.headD .OK_default) :: selBuiltinArgs el cl.tail

/-- `Selection.sel_known_builtin` -/
def selKnownBuiltin (bf : BuiltinFunction) (args : Exprlist) : Option Expr :=
  match bf, args with
  | .BI_platform b, _ => platformBuiltin b args
  | .BI_standard (.BI_select ty), a1 ::: a2 ::: a3 ::: Enil => some (selSelect ty a1 a2 a3)
  | .BI_standard .BI_fabs, a1 ::: Enil => some (absf a1)
  | .BI_standard .BI_fabsf, a1 ::: Enil => some (absfs a1)
  | _, _ => none

/-- `Selection.Sno_op` -/
def SnoOp : Stmt := Sseq Sskip Sskip

/-- `Selection.sel_builtin_default` -/
def selBuiltinDefault (optid : Option Ident) (ef : ExtFun) (args : List Cminor.Expr) : Stmt :=
  Sbuiltin (selBuiltinRes optid) ef (selBuiltinArgs opts args (builtinConstraints ef))

/-- `Selection.sel_builtin` -/
def selBuiltin (optid : Option Ident) (ef : ExtFun) (args : List Cminor.Expr) : Stmt :=
  match ef with
  | .EF_builtin name sg =>
      match lookupBuiltinFunction name sg with
      | some bf =>
          match optid with
          | some id =>
              match selKnownBuiltin bf (selExprlist opts args) with
              | some a => Sassign id a
              | none => selBuiltinDefault opts optid ef args
          | none => SnoOp
      | none => selBuiltinDefault opts optid ef args
  | _ => selBuiltinDefault opts optid ef args

/-! ## Switch statements -/

section SEL_SWITCH
variable (makeCmpEq : Expr → Z → Expr) (makeCmpLtu : Expr → Z → Expr)
  (makeSub : Expr → Z → Expr) (makeToInt : Expr → Expr)

/-- `Selection.sel_switch` -/
def selSwitch (arg : Nat) : Switch.Comptree → Exitexpr
  | .CTaction act => XEexit act
  | .CTifeq key act t' =>
      XEcondition (condexprOfExpr (makeCmpEq (Eletvar arg) key)) (XEexit act) (selSwitch arg t')
  | .CTiflt key t1 t2 =>
      XEcondition (condexprOfExpr (makeCmpLtu (Eletvar arg) key)) (selSwitch arg t1)
        (selSwitch arg t2)
  | .CTjumptable ofs sz tbl t' =>
      XElet (makeSub (Eletvar arg) ofs)
        (XEcondition (condexprOfExpr (makeCmpLtu (Eletvar 0) sz))
          (XEjumptable (makeToInt (Eletvar 0)) tbl)
          (selSwitch (arg + 1) t'))

end SEL_SWITCH

/-- `Selection.sel_switch_int` -/
def selSwitchInt : Nat → Switch.Comptree → Exitexpr :=
  selSwitch
    (fun arg n => comp .Ceq arg (Eop (.Ointconst (Integers.Int.repr n)) Enil))
    (fun arg n => compu .Clt arg (Eop (.Ointconst (Integers.Int.repr n)) Enil))
    (fun arg ofs => sub arg (Eop (.Ointconst (Integers.Int.repr ofs)) Enil))
    (fun arg => arg)

/-- `Selection.sel_switch_long` -/
def selSwitchLong : Nat → Switch.Comptree → Exitexpr :=
  selSwitch
    (fun arg n => cmpl .Ceq arg (longconst (Integers.Int64.repr n)))
    (fun arg n => cmplu .Clt arg (longconst (Integers.Int64.repr n)))
    (fun arg ofs => subl arg (longconst (Integers.Int64.repr ofs)))
    lowlong

/-! ## If-conversion -/

/-- `Selection.if_conversion_base` -/
def ifConversionBase (ki : KnownIdents) (env : Typenv) (cond : Cminor.Expr) (id : Ident)
    (ifso ifnot : Cminor.Expr) (kont : Stmt) : Option Stmt :=
  let ty := env id
  if selectSupported ty && isKnown ki id && safeExpr ki ifso && safeExpr ki ifnot
      && opts.ifConversionHeuristic id cond ifso ifnot ty kont
  then some (Sassign id (selSelectExpr opts ty cond ifso ifnot))
  else none

/-- `Selection.if_conversion` -/
def ifConversion (ki : KnownIdents) (env : Typenv) (cond : Cminor.Expr)
    (ifso ifnot : Cminor.Stmt) (kont : Stmt) : Option Stmt :=
  match classifyStmt ifso, classifyStmt ifnot with
  | .SCskip, .SCassign id a => ifConversionBase opts ki env cond id (.Evar id) a kont
  | .SCassign id a, .SCskip => ifConversionBase opts ki env cond id a (.Evar id) kont
  | .SCassign id1 a1, .SCassign id2 a2 =>
      if id1 = id2 then ifConversionBase opts ki env cond id1 a1 a2 kont else none
  | _, _ => none

/-! ## Statements -/

/-- `Selection.sel_stmt` -/
def selStmt (defmap : PTree Globdef) (ki : KnownIdents) (env : Typenv) :
    Cminor.Stmt → Stmt → Res Stmt
  | .Sskip, _ => .OK Sskip
  | .Sassign id e, _ => .OK (Sassign id (selExpr opts e))
  | .Sstore chunk addr rhs, _ => .OK (store opts chunk (selExpr opts addr) (selExpr opts rhs))
  | .Scall optid sg fn args, _ =>
      .OK (match classifyCall defmap fn with
        | .Call_default => Scall optid sg (.inl (selExpr opts fn)) (selExprlist opts args)
        | .Call_imm id => Scall optid sg (.inr id) (selExprlist opts args)
        | .Call_builtin ef => selBuiltin opts optid ef args)
  | .Sbuiltin optid ef args, _ => .OK (selBuiltin opts optid ef args)
  | .Stailcall sg fn args, _ =>
      .OK (match classifyCall defmap fn with
        | .Call_imm id => Stailcall sg (.inr id) (selExprlist opts args)
        | _ => Stailcall sg (.inl (selExpr opts fn)) (selExprlist opts args))
  | .Sseq s1 s2, k => do
      let s2' ← selStmt defmap ki env s2 k
      let s1' ← selStmt defmap ki env s1 s2'
      .OK (Sseq s1' s2')
  | .Sifthenelse e ifso ifnot, k =>
      match ifConversion opts ki env e ifso ifnot k with
      | some s => .OK s
      | none => do
          let ifso' ← selStmt defmap ki env ifso k
          let ifnot' ← selStmt defmap ki env ifnot k
          .OK (Sifthenelse (condexprOfExpr (selExpr opts e)) ifso' ifnot')
  | .Sloop body, _ => do
      let body' ← selStmt defmap ki env body Sskip
      .OK (Sloop body')
  | .Sblock body, k => do
      let body' ← selStmt defmap ki env body k
      .OK (Sblock body')
  | .Sexit n, _ => .OK (Sexit n)
  | .Sswitch false e cases dfl, _ =>
      let t := opts.compileSwitch Integers.Int.modulus dfl cases
      if Switch.validateSwitch Integers.Int.modulus dfl cases t
      then .OK (Sswitch (XElet (selExpr opts e) (selSwitchInt 0 t)))
      else .Error "Selection: bad switch (int)"
  | .Sswitch true e cases dfl, _ =>
      let t := opts.compileSwitch Integers.Int64.modulus dfl cases
      if Switch.validateSwitch Integers.Int64.modulus dfl cases t
      then .OK (Sswitch (XElet (selExpr opts e) (selSwitchLong 0 t)))
      else .Error "Selection: bad switch (long)"
  | .Sreturn none, _ => .OK (Sreturn none)
  | .Sreturn (some e), _ => .OK (Sreturn (some (selExpr opts e)))
  | .Slabel lbl body, k => do
      let body' ← selStmt defmap ki env body k
      .OK (Slabel lbl body')
  | .Sgoto lbl, _ => .OK (Sgoto lbl)

end SELECTION

/-! ## Functions and programs -/

/-- `Selection.sel_function` -/
def selFunction (opts : Options) (dm : PTree Globdef) (_hf : HelperFunctions)
    (f : Cminor.Function) : Res CminorSel.Function := do
  let ki := CC.Selection.knownId f
  let env ← typeFunction f
  let body' ← selStmt opts dm ki env f.fn_body Sskip
  .OK { fn_sig := f.fn_sig, fn_params := f.fn_params, fn_vars := f.fn_vars,
        fn_stackspace := f.fn_stackspace, fn_body := body' }

/-- `Selection.sel_fundef` -/
def selFundef (opts : Options) (dm : PTree Globdef) (hf : HelperFunctions)
    (f : Cminor.Fundef) : Res CminorSel.Fundef :=
  ASTFundef.transfPartial (selFunction opts dm hf) f

/-- `Selection.sel_program` -/
def selProgram (opts : Options) (p : Cminor.Program) : Res CminorSel.Program := do
  let dm := p.defmap
  let hf ← getHelpers dm
  transformPartialProgram (selFundef opts dm hf) p

end Selection
end RiscV
end CC
