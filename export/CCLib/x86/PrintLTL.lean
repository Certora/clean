/-
  Pretty-printer for LTL code — port of `backend/PrintLTL.ml`.

  The printing functions return strings instead of writing to an
  `out_channel`.  `print_if` (option `-dltl`) is `printIf`, with the
  destination file as an argument.

  This is the copy for the x86-64 back end (`CCLib/x86/`) of
  `CCLib/backend/PrintLTL.lean`.
-/
import CCLib.x86.LTL
import CCLib.x86.PrintOp
import CCLib.x86.Machregsaux

namespace CC
namespace X86
namespace PrintLTL

open Camlcoq PrintAST PrintOp

/-- `PrintLTL.mreg` -/
def mreg (r : Mreg) : String :=
  match Machregsaux.nameOfRegister r with
  | some s => s
  | none => "<unknown machreg>"

/-- `PrintLTL.mregs` -/
def mregs (rl : List Mreg) : String := ", ".intercalate (rl.map mreg)

/-- `PrintLTL.slot` -/
def slot (sl : Slot) (ofs : Z) (ty : ATyp) : String :=
  match sl with
  | .Local => s!"local({ci32 ofs},{nameOfType ty})"
  | .Incoming => s!"incoming({ci32 ofs},{nameOfType ty})"
  | .Outgoing => s!"outgoing({ci32 ofs},{nameOfType ty})"

/-- `PrintLTL.loc` -/
def loc : Loc → String
  | .R r => mreg r
  | .S sl ofs ty => slot sl ofs ty

/-- `PrintLTL.locs` -/
def locs (ll : List Loc) : String := ", ".intercalate (ll.map loc)

/-- `PrintLTL.ros` -/
def ros : Sum Mreg Ident → String
  | .inl r => mreg r
  | .inr s => s!"\"{externAtom s}\""

/-- `PrintLTL.print_succ` -/
def printSucc (s : Positive) (dfl : Int) : String :=
  if (s.toNat : Int) ≠ dfl then s!"goto {s.toNat}" else ""

/-- `PrintLTL.print_instruction` -/
def printInstruction (succ : Int) : LTL.Instruction → String
  | .Lop op args res => s!"{mreg res} = {printOperation mreg op args}"
  | .Lload chunk addr args dst =>
    s!"{mreg dst} = {nameOfChunk chunk}[{printAddressing mreg addr args}]"
  | .Lgetstack sl ofs ty dst => s!"{mreg dst} = {slot sl ofs ty}"
  | .Lsetstack src sl ofs ty => s!"{slot sl ofs ty} = {mreg src}"
  | .Lstore chunk addr args src =>
    s!"{nameOfChunk chunk}[{printAddressing mreg addr args}] = {mreg src}"
  | .Lcall _ fn => s!"call {ros fn}"
  | .Ltailcall _ fn => s!"tailcall {ros fn}"
  | .Lbuiltin ef args res =>
    s!"{printBuiltinRes mreg res} = {nameOfExternal ef}({printBuiltinArgs loc args})"
  | .Lbranch s => printSucc s succ
  | .Lcond cond args s1 s2 =>
    s!"if ({printCondition mreg cond args}) goto {s1.toNat} else goto {s2.toNat}"
  | .Ljumptable arg tbl =>
    s!"jumptable ({mreg arg})" ++
      String.join ((List.range tbl.length).zip tbl |>.map fun (i, l) =>
        s!"\n\t\tcase {i}: goto {l.toNat}")
  | .Lreturn => "return"

/-- `PrintLTL.print_instructions` -/
def printInstructions (succ : Int) (il : List LTL.Instruction) : String :=
  "; ".intercalate (il.map (printInstruction succ))

/-- `PrintLTL.print_block` -/
def printBlock (pc : Nat) (blk : LTL.Bblock) : String :=
  lpad 5 (toString pc) ++ ":\t" ++ printInstructions ((pc : Int) - 1) blk ++ "\n"

/-- `PrintLTL.print_function` -/
def printFunction (id : Ident) (f : LTL.Function) : String :=
  let instrs : List (Nat × LTL.Bblock) :=
    ((PTree.elements f.fn_code).map fun (pc, b) => (pc.toNat, b)).mergeSort
    (fun a b => a.1 ≥ b.1)
  s!"{externAtom id}() \{\n" ++
  printSucc f.fn_entrypoint (match instrs with | (pc1, _) :: _ => (pc1 : Int) | [] => -1) ++
  String.join (instrs.map fun (pc, b) => printBlock pc b) ++
  "}\n\n"

/-- `PrintLTL.print_globdef` -/
def printGlobdef : Ident × GlobDef LTL.Fundef Unit → String
  | (id, .Gfun (.Internal f)) => printFunction id f
  | _ => ""

/-- `PrintLTL.print_program` -/
def printProgram (prog : LTL.Program) : String :=
  String.join (prog.prog_defs.map printGlobdef)

/-- `PrintLTL.print_if` -/
def printIf (destination : Option String) (prog : LTL.Program) : IO Unit :=
  match destination with
  | none => pure ()
  | some f => IO.FS.writeFile f (printProgram prog)

end PrintLTL
end X86
end CC
