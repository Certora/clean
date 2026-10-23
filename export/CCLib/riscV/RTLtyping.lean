/-
  [RISC-V instance of `CCLib/backend/RTLtyping.lean`: the same development, in
  namespace `CC.RiscV`, over the RISC-V operators, registers and conventions.]

  Type inference for RTL — port of the executable parts of
  `backend/RTLtyping.v`: `regenv`, `type_of_builtin_arg`,
  `type_of_builtin_res`, `S` (the unification solver at machine types),
  `check_successor(s)`, `type_ros`, `is_move`, `type_expect`,
  `type_builtin_arg(s)`, `type_builtin_res`, `type_instr`, `type_code`,
  `check_params_norepet`, `type_function`.

  The relational typing (`wt_instr`, `wt_function`, …) and the soundness of
  `type_function` are in `backend/RTLtypingSound.lean`; the typing of RTL
  states and subject reduction in `backend/RTLtypingSubject.lean`.  The
  completeness of `type_function` is not ported.

  Differences from Rocq: `Archi.abi` (used by `tailcall_is_possible`) is
  an explicit argument `abi`; error messages are plain strings.
-/
import CCLib.riscV.RTL
import CCLib.common.Unityping
import CCLib.riscV.Conventions

namespace CC
namespace RiscV
namespace RTLtyping

open RTL Op

/-- `RTLtyping.regenv` -/
abbrev Regenv := Reg → ATyp

/-- `RTLtyping.type_of_builtin_arg` -/
def typeOfBuiltinArg (env : Regenv) (a : BuiltinArg Reg) : ATyp :=
  match a with
  | .BA r => env r
  | .BA_int _ => .Tint
  | .BA_long _ => .Tlong
  | .BA_float _ => .Tfloat
  | .BA_single _ => .Tsingle
  | .BA_loadstack chunk _ => chunk.typ
  | .BA_addrstack _ => Tptr
  | .BA_loadglobal chunk _ _ => chunk.typ
  | .BA_addrglobal _ _ => Tptr
  | .BA_splitlong _ _ => .Tlong
  | .BA_addptr _ _ => Tptr

/-- `RTLtyping.type_of_builtin_res` -/
def typeOfBuiltinRes (env : Regenv) (r : BuiltinRes Reg) : ATyp :=
  match r with
  | .BR r => env r
  | _ => .Tint

/-- `RTLtyping.S.typenv` -/
abbrev STypenv := UniSolver.Typenv ATyp

section INFERENCE
variable (f : RTL.Function)

/-- `RTLtyping.check_successor` -/
def checkSuccessor (s : Node) : Res Unit :=
  match f.fn_code.get s with
  | none => .Error "bad successor"
  | some _ => .OK ()

/-- `RTLtyping.check_successors` -/
def checkSuccessors : List Node → Res Unit
  | [] => .OK ()
  | s1 :: sl' => do checkSuccessor f s1; checkSuccessors sl'

/-- `RTLtyping.type_ros` -/
def typeRos (e : STypenv) (ros : Sum Reg Ident) : Res STypenv :=
  match ros with
  | .inl r => UniSolver.set e r Tptr
  | .inr _ => .OK e

/-- `RTLtyping.is_move` -/
def isMove (op : Operation) : Bool :=
  match op with
  | .Omove => true
  | _ => false

/-- `RTLtyping.type_expect` -/
def typeExpect (e : STypenv) (t1 t2 : ATyp) : Res STypenv :=
  if t1 = t2 then .OK e else .Error "unexpected type"

/-- `RTLtyping.type_builtin_arg` -/
def typeBuiltinArg (e : STypenv) (a : BuiltinArg Reg) (ty : ATyp) : Res STypenv :=
  match a with
  | .BA r => UniSolver.set e r ty
  | .BA_int _ => typeExpect e ty .Tint
  | .BA_long _ => typeExpect e ty .Tlong
  | .BA_float _ => typeExpect e ty .Tfloat
  | .BA_single _ => typeExpect e ty .Tsingle
  | .BA_loadstack chunk _ => typeExpect e ty chunk.typ
  | .BA_addrstack _ => typeExpect e ty Tptr
  | .BA_loadglobal chunk _ _ => typeExpect e ty chunk.typ
  | .BA_addrglobal _ _ => typeExpect e ty Tptr
  | .BA_splitlong _ _ => typeExpect e ty .Tlong
  | .BA_addptr _ _ => typeExpect e ty Tptr

/-- `RTLtyping.type_builtin_args` -/
def typeBuiltinArgs : STypenv → List (BuiltinArg Reg) → List ATyp → Res STypenv
  | e, [], [] => .OK e
  | e, a1 :: al, ty1 :: tyl => do
      let e1 ← typeBuiltinArg e a1 ty1
      typeBuiltinArgs e1 al tyl
  | _, _, _ => .Error "builtin arity mismatch"

/-- `RTLtyping.type_builtin_res` -/
def typeBuiltinRes (e : STypenv) (a : BuiltinRes Reg) (ty : ATyp) : Res STypenv :=
  match a with
  | .BR r => UniSolver.set e r ty
  | _ => typeExpect e ty .Tint

/-- `AST.proj_sig_args` -/
def projSigArgs (sg : Signature) : List ATyp := sg.sig_args.map XType.proj
/-- `AST.proj_sig_res` -/
def projSigRes (sg : Signature) : ATyp := sg.sig_res.proj

/-- `RTLtyping.type_instr` -/
def typeInstr (e : STypenv) (i : Instruction) : Res STypenv :=
  match i with
  | .Inop s => do checkSuccessor f s; .OK e
  | .Iop op args res s => do
      checkSuccessor f s
      if isMove op then
        match args with
        | [arg] => do
            let (_, e') ← UniSolver.move e res arg
            .OK e'
        | _ => .Error "ill-formed move"
      else
        let (targs, tres) := typeOfOperation op
        let e1 ← UniSolver.setList e args targs
        UniSolver.set e1 res tres
  | .Iload chunk addr args dst s => do
      checkSuccessor f s
      let e1 ← UniSolver.setList e args (typeOfAddressing addr)
      UniSolver.set e1 dst chunk.typ
  | .Istore chunk addr args src s => do
      checkSuccessor f s
      let e1 ← UniSolver.setList e args (typeOfAddressing addr)
      UniSolver.set e1 src chunk.typ
  | .Icall sig ros args res s => do
      checkSuccessor f s
      let e1 ← typeRos e ros
      let e2 ← UniSolver.setList e1 args (projSigArgs sig)
      UniSolver.set e2 res (projSigRes sig)
  | .Itailcall sig ros args => do
      let e1 ← typeRos e ros
      let e2 ← UniSolver.setList e1 args (projSigArgs sig)
      if sig.sig_res = f.fn_sig.sig_res then
        if Conventions.tailcallIsPossible  sig then .OK e2
        else .Error "tailcall not possible"
      else .Error "bad return type in tailcall"
  | .Ibuiltin ef args res s => do
      let sig := ef.sig
      checkSuccessor f s
      let e1 ← match ef with
        | .EF_annot _ _ _ | .EF_debug _ _ _ => .OK e
        | _ => typeBuiltinArgs e args (projSigArgs sig)
      typeBuiltinRes e1 res (projSigRes sig)
  | .Icond cond args s1 s2 => do
      checkSuccessor f s1
      checkSuccessor f s2
      UniSolver.setList e args (typeOfCondition cond)
  | .Ijumptable arg tbl => do
      checkSuccessors f tbl
      let e1 ← UniSolver.set e arg .Tint
      if (tbl.length : Z) * 4 ≤ Integers.Int.max_unsigned then .OK e1
      else .Error "jumptable too big"
  | .Ireturn optres =>
      match optres, decide (f.fn_sig.sig_res = .Xvoid) with
      | none, true => .OK e
      | some r, false => UniSolver.set e r (projSigRes f.fn_sig)
      | _, _ => .Error "bad return"

/-- `RTLtyping.type_code` -/
def typeCode (e : STypenv) : Res STypenv :=
  PTree.fold (fun re _pc i =>
    match re with
    | .Error _ => re
    | .OK e =>
        match typeInstr  f e i with
        | .Error msg => .Error ("At PC: " ++ msg)
        | .OK e' => .OK e')
    f.fn_code (.OK e)

/-- `RTLtyping.check_params_norepet` -/
def checkParamsNorepet (params : List Reg) : Res Unit :=
  if params.Nodup then .OK () else .Error "duplicate parameters"

/-- `RTLtyping.type_function` -/
def typeFunction : Res Regenv := do
  let e1 ← typeCode  f UniSolver.initial
  let e2 ← UniSolver.setList e1 f.fn_params (projSigArgs f.fn_sig)
  let te ← UniSolver.solve .Tint e2
  checkParamsNorepet f.fn_params
  checkSuccessor f f.fn_entrypoint
  .OK te

end INFERENCE

end RTLtyping
end RiscV
end CC
