/-
  Constant propagation over RTL — port of `backend/Constprop.v`
  (definitions).

  Ported: `transf_ros`, `successor_rec`, `num_iter`, `successor`,
  `builtin_arg_reduction`, `builtin_arg_strength_reduction`,
  `builtin_args_strength_reduction`, `debug_strength_reduction`,
  `builtin_strength_reduction`, `transf_instr`, `transf_function`,
  `transf_fundef`, `transf_program`.
  Correctness proof: `Constpropproof.lean`, `ConstpropproofStep.lean`.

  Differences from Rocq: the OCaml parameters are the fields of
  `ConstpropOp.Options`; `Archi.abi` (used by the value analysis to
  initialize the parameters) is an explicit argument `abi`.
-/
import CCLib.aarch64.ConstpropOp
import CCLib.backend.ValueAnalysis
import CCLib.aarch64.Machregs
import CCLib.backend.Tailcall
import CCLib.backend.CminorSel

namespace CC
namespace Constprop

open ValueDomain ValueAnalysis RTL ConstpropOp

section
variable (o : ConstpropOp.Options)

/-- `Constprop.transf_ros` -/
def transfRos (ae : Aenv) (ros : Sum Reg Ident) : Sum Reg Ident :=
  match ros with
  | .inl r =>
      match areg ae r with
      | .Ptr (.Gl symb ofs) => if Integers.Ptrofs.eq ofs Integers.Ptrofs.zero then .inr symb else ros
      | _ => ros
  | .inr _ => ros

/-- `Constprop.successor_rec` -/
def successorRec : Nat → RTL.Function → Aenv → Node → Node
  | 0, _, _, pc => pc
  | n' + 1, f, ae, pc =>
      match f.fn_code.get pc with
      | some (.Inop s) => successorRec n' f ae s
      | some (.Icond cond args s1 s2) =>
          match resolveBranch (ValueAOp.evalStaticCondition o.toOptions cond (aregs ae args)) with
          | some b => successorRec n' f ae (if b then s1 else s2)
          | none => pc
      | _ => pc

/-- `Constprop.num_iter` -/
def numIter : Nat := 10

/-- `Constprop.successor`: jump over conditionals that can be resolved. -/
def successor (f : RTL.Function) (ae : Aenv) (pc : Node) : Node :=
  successorRec o numIter f ae pc

/-- `Constprop.builtin_arg_reduction` -/
def builtinArgReduction (ae : Aenv) : BuiltinArg Reg → BuiltinArg Reg
  | a@(.BA r) =>
      match areg ae r with
      | .I n => .BA_int n
      | .L n => .BA_long n
      | .F n => if o.generateFloatConstants then .BA_float n else a
      | .FS n => if o.generateFloatConstants then .BA_single n else a
      | _ => a
  | .BA_splitlong hi lo =>
      match builtinArgReduction ae hi, builtinArgReduction ae lo with
      | .BA_int nhi, .BA_int nlo => .BA_long (Integers.Int64.ofwords nhi nlo)
      | hi', lo' => .BA_splitlong hi' lo'
  | .BA_addptr a1 a2 => .BA_addptr (builtinArgReduction ae a1) (builtinArgReduction ae a2)
  | a => a

/-- `Constprop.builtin_arg_strength_reduction` -/
def builtinArgStrengthReduction (ae : Aenv) (a : BuiltinArg Reg) (c : BuiltinArgConstraint) :
    BuiltinArg Reg :=
  let a' := builtinArgReduction o ae a
  if Op.builtinArgOk a' c then a' else a

/-- `Constprop.builtin_args_strength_reduction` -/
def builtinArgsStrengthReduction (ae : Aenv) :
    List (BuiltinArg Reg) → List BuiltinArgConstraint → List (BuiltinArg Reg)
  | [], _ => []
  | a :: al, cl =>
      builtinArgStrengthReduction o ae a (cl.headD .OK_default) ::
        builtinArgsStrengthReduction ae al cl.tail

/-- `Constprop.debug_strength_reduction`: for debug annotations, constant
    values are added to the original information. -/
def debugStrengthReduction (ae : Aenv) : List (BuiltinArg Reg) → List (BuiltinArg Reg)
  | [] => []
  | a :: al =>
      let a' := builtinArgReduction o ae a
      let al' := a :: debugStrengthReduction ae al
      match a, a' with
      | .BA _, .BA_int _ | .BA _, .BA_long _ | .BA _, .BA_float _ | .BA _, .BA_single _ =>
          a' :: al'
      | _, _ => al'

/-- `Constprop.builtin_strength_reduction` -/
def builtinStrengthReduction (ae : Aenv) (ef : ExtFun) (al : List (BuiltinArg Reg)) :
    List (BuiltinArg Reg) :=
  match ef with
  | .EF_debug _ _ _ => debugStrengthReduction o ae al
  | _ => builtinArgsStrengthReduction o ae al (builtinConstraints ef)

/-- `Constprop.transf_instr` -/
def transfInstr (f : RTL.Function) (an : PMap VAState) (rm : Romem) (pc : Node)
    (instr : Instruction) : Instruction :=
  match an.get pc with
  | .Bot => instr
  | .State ae am =>
      match instr with
      | .Iop op args res s =>
          let aargs := aregs ae args
          let a := ValueAOp.evalStaticOperation o.toOptions op aargs
          let s' := successor o f (AE.set res a ae) s
          match constForResult o a with
          | some cop => .Iop cop [] res s'
          | none =>
              let (op', args') := opStrengthReduction o op args aargs
              .Iop op' args' res s'
      | .Iload chunk addr args dst s =>
          let aargs := aregs ae args
          let a := loadv o.strict chunk rm am (ValueAOp.evalStaticAddressing addr aargs)
          match constForResult o a with
          | some cop => .Iop cop [] dst s
          | none =>
              let (addr', args') := addrStrengthReduction o addr args aargs
              .Iload chunk addr' args' dst s
      | .Istore chunk addr args src s =>
          let aargs := aregs ae args
          let (addr', args') := addrStrengthReduction o addr args aargs
          .Istore chunk addr' args' src s
      | .Icall sig ros args res s => .Icall sig (transfRos ae ros) args res s
      | .Itailcall sig ros args => .Itailcall sig (transfRos ae ros) args
      | .Ibuiltin ef args res s =>
          let dfl := Instruction.Ibuiltin ef (builtinStrengthReduction o ae ef args) res s
          match ef, res with
          | .EF_builtin name sg, .BR rd =>
              match Builtins.lookupBuiltinFunction name sg with
              | some bf =>
                  match evalStaticBuiltinFunction o.toOptions ae am rm bf args with
                  | some a =>
                      match constForResult o a with
                      | some cop => .Iop cop [] rd s
                      | none => dfl
                  | none => dfl
              | none => dfl
          | _, _ => dfl
      | .Icond cond args s1 s2 =>
          let aargs := aregs ae args
          match resolveBranch (ValueAOp.evalStaticCondition o.toOptions cond aargs) with
          | some b => if b then .Inop s1 else .Inop s2
          | none =>
              let (cond', args') := condStrengthReduction cond args aargs
              .Icond cond' args' s1 s2
      | .Ijumptable arg tbl =>
          match areg ae arg with
          | .I n =>
              match CminorSel.listNthZ tbl (Integers.Int.unsigned n) with
              | some s => .Inop s
              | none => instr
          | _ => instr
      | _ => instr

/-- `Constprop.transf_function` -/
def transfFunction (abi : Conventions1.AbiKind) (rm : Romem) (f : RTL.Function) :
    RTL.Function :=
  let an := ValueAnalysis.analyze o.toOptions abi rm f
  RTL.transfFunction (transfInstr o f an rm) f

/-- `Constprop.transf_fundef` -/
def transfFundef (abi : Conventions1.AbiKind) (rm : Romem) (fd : RTL.Fundef) : RTL.Fundef :=
  ASTFundef.transf (transfFunction o abi rm) fd

/-- `Constprop.transf_program` -/
def transfProgram (abi : Conventions1.AbiKind) (p : RTL.Program) : RTL.Program :=
  let rm := romemFor o.toOptions p
  transformProgram (transfFundef o abi rm) p

end

end Constprop
end CC
