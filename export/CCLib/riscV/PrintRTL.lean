/-
  Pretty-printer for RTL code — port of `backend/PrintRTL.ml`.

  The printing functions return strings instead of writing to an
  `out_channel`.  `print_if`, which writes the program to the file named by
  the `-drtl` option, is `printIf`; the option value (`destination`) is an
  argument.

  This is the copy for the RISC-V back end (`CCLib/riscV/`) of
  `CCLib/backend/PrintRTL.lean`.
-/
import CCLib.riscV.RTL
import CCLib.riscV.PrintOp

namespace CC
namespace RiscV
namespace PrintRTL

open Camlcoq PrintAST RTL

/-- `PrintRTL.reg` -/
def reg (r : Reg) : String := s!"x{r.toNat}"

/-- `PrintRTL.regs` -/
def regs (rl : List Reg) : String := ", ".intercalate (rl.map reg)

/-- `PrintRTL.ros` -/
def ros : Sum Reg Ident → String
  | .inl r => reg r
  | .inr s => s!"\"{externAtom s}\""

/-- `PrintRTL.print_succ` -/
def printSucc (s : Node) (dfl : Int) : String :=
  if (s.toNat : Int) ≠ dfl then s!"\tgoto {s.toNat}\n" else ""

/-- `PrintRTL.print_instruction` -/
def printInstruction (pc : Nat) (i : RTL.Instruction) : String :=
  let dfl : Int := (pc : Int) - 1
  lpad 5 (toString pc) ++ ":\t" ++
  match i with
  | .Inop s =>
    if (s.toNat : Int) = dfl then "nop\n" else s!"goto {s.toNat}\n"
  | .Iop op args res s =>
    s!"{reg res} = {PrintOp.printOperation reg op args}\n" ++ printSucc s dfl
  | .Iload chunk addr args dst s =>
    s!"{reg dst} = {nameOfChunk chunk}[{PrintOp.printAddressing reg addr args}]\n" ++
      printSucc s dfl
  | .Istore chunk addr args src s =>
    s!"{nameOfChunk chunk}[{PrintOp.printAddressing reg addr args}] = {reg src}\n" ++
      printSucc s dfl
  | .Icall _ fn args res s =>
    s!"{reg res} = {ros fn}({regs args})\n" ++ printSucc s dfl
  | .Itailcall _ fn args => s!"tailcall {ros fn}({regs args})\n"
  | .Ibuiltin ef args res s =>
    s!"{printBuiltinRes reg res} = {nameOfExternal ef}({printBuiltinArgs reg args})\n" ++
      printSucc s dfl
  | .Icond cond args s1 s2 =>
    s!"if ({PrintOp.printCondition reg cond args}) goto {s1.toNat} else goto {s2.toNat}\n"
  | .Ijumptable arg tbl =>
    s!"jumptable ({reg arg})\n" ++
      String.join ((List.range tbl.length).zip tbl |>.map fun (i, l) =>
        s!"\t\tcase {i}: goto {l.toNat}\n")
  | .Ireturn none => "return\n"
  | .Ireturn (some arg) => s!"return {reg arg}\n"

/-- The instructions of a function, by decreasing program point (as
    `print_function` sorts them). -/
def sortedInstrs (f : RTL.Function) : List (Nat × RTL.Instruction) :=
  ((PTree.elements f.fn_code).map fun (pc, i) => (pc.toNat, i)).mergeSort
    (fun a b => a.1 ≥ b.1)

/-- `PrintRTL.print_function` -/
def printFunction (id : Ident) (f : RTL.Function) : String :=
  let instrs := sortedInstrs f
  s!"{externAtom id}({regs f.fn_params}) \{\n" ++
  printSucc f.fn_entrypoint (match instrs with | (pc1, _) :: _ => (pc1 : Int) | [] => -1) ++
  String.join (instrs.map fun (pc, i) => printInstruction pc i) ++
  "}\n\n"

/-- `PrintRTL.print_globdef` -/
def printGlobdef : Ident × GlobDef RTL.Fundef Unit → String
  | (id, .Gfun (.Internal f)) => printFunction id f
  | _ => ""

/-- `PrintRTL.print_program` -/
def printProgram (prog : RTL.Program) : String :=
  String.join (prog.prog_defs.map printGlobdef)

/-- `PrintRTL.print_if`: write the program to `<destination>.<passno>`. -/
def printIf (destination : Option String) (passno : Int) (prog : RTL.Program) : IO Unit :=
  match destination with
  | none => pure ()
  | some f => IO.FS.writeFile (f ++ "." ++ toString passno) (printProgram prog)

end PrintRTL
end RiscV
end CC
