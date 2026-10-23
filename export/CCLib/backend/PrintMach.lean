/-
  Pretty-printer for Mach code — port of `backend/PrintMach.ml`.

  The printing functions return strings instead of writing to an
  `out_channel`.  `print_if` (option `-dmach`) is `printIf`, with the
  destination file as an argument.
-/
import CCLib.backend.Mach
import CCLib.aarch64.PrintOp
import CCLib.aarch64.Machregsaux

namespace CC
namespace PrintMach

open Camlcoq PrintAST

/-- `PrintMach.reg` -/
def reg (r : Mreg) : String :=
  match Machregsaux.nameOfRegister r with
  | some s => s
  | none => "<unknown reg>"

/-- `PrintMach.regs` -/
def regs (rl : List Mreg) : String := ", ".intercalate (rl.map reg)

/-- `PrintMach.ros` -/
def ros : Sum Mreg Ident → String
  | .inl r => reg r
  | .inr s => s!"\"{externAtom s}\""

/-- `PrintMach.print_instruction` -/
def printInstruction : Mach.Instruction → String
  | .Mgetstack ofs ty res => s!"\t{reg res} = stack({ci32 ofs}, {nameOfType ty})\n"
  | .Msetstack arg ofs ty => s!"\tstack({ci32 ofs}, {nameOfType ty}) = {reg arg}\n"
  | .Mgetparam ofs ty res => s!"\t{reg res} = param({ci32 ofs}, {nameOfType ty})\n"
  | .Mop op args res => s!"\t{reg res} = {PrintOp.printOperation reg op args}\n"
  | .Mload chunk addr args dst =>
    s!"\t{reg dst} = {nameOfChunk chunk}[{PrintOp.printAddressing reg addr args}]\n"
  | .Mstore chunk addr args src =>
    s!"\t{nameOfChunk chunk}[{PrintOp.printAddressing reg addr args}] = {reg src}\n"
  | .Mcall _ fn => s!"\tcall {ros fn}\n"
  | .Mtailcall _ fn => s!"\ttailcall {ros fn}\n"
  | .Mbuiltin ef args res =>
    s!"\t{printBuiltinRes reg res} = {nameOfExternal ef}({printBuiltinArgs reg args})\n"
  | .Mlabel lbl => lpad 5 (toString lbl.toNat) ++ ":"
  | .Mgoto lbl => s!"\tgoto {lbl.toNat}\n"
  | .Mcond cond args lbl =>
    s!"\tif ({PrintOp.printCondition reg cond args}) goto {lbl.toNat}\n"
  | .Mjumptable arg tbl =>
    s!"\tjumptable ({reg arg})\n" ++
      String.join ((List.range tbl.length).zip tbl |>.map fun (i, l) =>
        s!"\t\tcase {i}: goto {l.toNat}\n")
  | .Mreturn => "\treturn\n"

/-- `PrintMach.print_function` -/
def printFunction (id : Ident) (f : Mach.Function) : String :=
  s!"{externAtom id}() \{\n" ++ String.join (f.fn_code.map printInstruction) ++ "}\n\n"

/-- `PrintMach.print_globdef` -/
def printGlobdef : Ident × GlobDef Mach.Fundef Unit → String
  | (id, .Gfun (.Internal f)) => printFunction id f
  | _ => ""

/-- `PrintMach.print_program` -/
def printProgram (prog : Mach.Program) : String :=
  String.join (prog.prog_defs.map printGlobdef)

/-- `PrintMach.print_if` -/
def printIf (destination : Option String) (prog : Mach.Program) : IO Unit :=
  match destination with
  | none => pure ()
  | some f => IO.FS.writeFile f (printProgram prog)

end PrintMach
end CC
