/-
  Pretty-printer for XTL — port of `backend/PrintXTL.ml` (AArch64 back
  end).

  The printing functions return strings instead of writing to an
  `out_channel`.  The optional allocation and liveness information, kept in
  global references by OCaml (`current_alloc`, `current_liveness`), are
  arguments here.  Live sets are printed in increasing register order.
-/
import CCLib.backend.XTL
import CCLib.aarch64.PrintOp
import CCLib.aarch64.Machregsaux

namespace CC
namespace PrintXTL

open Camlcoq PrintAST PrintOp XTL

/-- `PrintXTL.mreg` -/
def mreg (r : Mreg) : String :=
  match Machregsaux.nameOfRegister r with
  | some s => s
  | none => "<unknown machreg>"

/-- `PrintXTL.short_name_of_type` -/
def shortNameOfType : ATyp → String
  | .Tint => "i"
  | .Tfloat => "f"
  | .Tlong => "l"
  | .Tsingle => "s"
  | .Tany32 => "w"
  | .Tany64 => "d"

/-- `PrintXTL.loc` -/
def loc : Loc → String
  | .R r => mreg r
  | .S .Local ofs ty => s!"L{shortNameOfType ty}{ci32 ofs}"
  | .S .Incoming ofs ty => s!"I{shortNameOfType ty}{ci32 ofs}"
  | .S .Outgoing ofs ty => s!"O{shortNameOfType ty}{ci32 ofs}"

section PRINT
-- `alloc`: the allocation to print next to the pseudo-registers, if any
-- (OCaml `current_alloc`).
variable (alloc : Option (Var → Loc))

/-- `PrintXTL.reg` -/
def reg (r : Reg) (ty : ATyp) : String :=
  match alloc with
  | none => s!"x{r.toNat}"
  | some a => s!"x{r.toNat}\{{loc (a (.V r ty))}}"

/-- `PrintXTL.var` -/
def var : Var → String
  | .V r ty => reg alloc r ty
  | .L l => loc l

/-- `PrintXTL.vars` -/
def vars (vl : List Var) : String := ", ".intercalate (vl.map (var alloc))

/-- `PrintXTL.ros` -/
def ros : Sum Var Ident → String
  | .inl r => var alloc r
  | .inr s => s!"\"{externAtom s}\""

/-- `PrintXTL.print_succ` -/
def printSucc (s : Positive) (dfl : Int) : String :=
  if (s.toNat : Int) ≠ dfl then s!"goto {s.toNat}" else ""

/-- `PrintXTL.print_instruction` -/
def printInstruction (succ : Int) : XTL.Instruction → String
  | .Xmove src dst => s!"{var alloc dst} = {var alloc src}"
  | .Xreload src dst => s!"{var alloc dst} =r {var alloc src}"
  | .Xspill src dst => s!"{var alloc dst} =s {var alloc src}"
  | .Xparmove srcs dsts t1 t2 =>
    s!"({vars alloc dsts}) = ({vars alloc srcs}) using {var alloc t1}, {var alloc t2}"
  | .Xop op args res => s!"{var alloc res} = {printOperation (var alloc) op args}"
  | .Xload chunk addr args dst =>
    s!"{var alloc dst} = {nameOfChunk chunk}[{printAddressing (var alloc) addr args}]"
  | .Xstore chunk addr args src =>
    s!"{nameOfChunk chunk}[{printAddressing (var alloc) addr args}] = {var alloc src}"
  | .Xcall _ fn args res => s!"{vars alloc res} = call {ros alloc fn}({vars alloc args})"
  | .Xtailcall _ fn args => s!"tailcall {ros alloc fn}({vars alloc args})"
  | .Xbuiltin ef args res =>
    s!"{printBuiltinRes (var alloc) res} = {nameOfExternal ef}({printBuiltinArgs (var alloc) args})"
  | .Xbranch s => printSucc s succ
  | .Xcond cond args s1 s2 =>
    s!"if ({printCondition (var alloc) cond args}) goto {s1.toNat} else goto {s2.toNat}"
  | .Xjumptable arg tbl =>
    s!"jumptable ({var alloc arg})" ++
      String.join ((List.range tbl.length).zip tbl |>.map fun (i, l) =>
        s!"\n\t\tcase {i}: goto {l.toNat}")
  | .Xreturn args => s!"return {vars alloc args}"

/-- `PrintXTL.print_instructions` -/
def printInstructions (succ : Int) (il : List XTL.Instruction) : String :=
  "; ".intercalate (il.map (printInstruction alloc succ))

/-- `PrintXTL.liveset` -/
def liveset (lv : VSet) : String :=
  let regs := (lv.toList.filterMap fun v => match v with
    | .V r _ => some r.toNat
    | .L _ => none).mergeSort (· ≤ ·)
  "{" ++ String.join (regs.map fun r => s!" x{r}") ++ " }"

/-- `PrintXTL.print_block` -/
def printBlock (live : Option (Std.HashMap XTL.Node VSet)) (pc : Positive) (blk : XTL.Block) :
    String :=
  lpad 5 (toString pc.toNat) ++ ":\t" ++ printInstructions alloc ((pc.toNat : Int) - 1) blk ++
    "\n" ++
  match live with
  | none => ""
  | some liveness => liveset (liveness.getD pc {}) ++ "\n"

/-- `PrintXTL.print_function` -/
def printFunction (live : Option (Std.HashMap XTL.Node VSet) := none) (f : XFunction) :
    String :=
  let instrs := (PTree.elements f.fn_code).mergeSort (fun a b => a.1.toNat ≥ b.1.toNat)
  "f() {\n" ++
  printSucc f.fn_entrypoint (match instrs with | (pc1, _) :: _ => (pc1.toNat : Int) | [] => -1) ++
  String.join (instrs.map fun (pc, b) => printBlock alloc live pc b) ++
  "}\n\n"

end PRINT

end PrintXTL
end CC
