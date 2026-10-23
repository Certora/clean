/-
  [RISC-V instance of `CCLib/backend/CleanupLabels.lean`: the same development, in
  namespace `CC.RiscV`, over the RISC-V operators, registers and conventions.]

  Removal of unreferenced labels in Linear code — port of
  `backend/CleanupLabels.v` (`add_label_branched_to`, `labels_branched_to`,
  `remove_unused`, `remove_unused_labels`, `cleanup_labels`,
  `transf_function`, `transf_fundef`, `transf_program`).

  Differences from Rocq: `Labelset` (an AVL set) is a `PTree Unit`.
-/
import CCLib.riscV.Linear
import CCLib.riscV.Tailcall

namespace CC
namespace RiscV
namespace CleanupLabels

open Linear

/-- `CleanupLabels.Labelset` -/
abbrev Labelset := PTree Unit

def Labelset.add (l : Label) (s : Labelset) : Labelset := s.set l ()
def Labelset.mem (l : Label) (s : Labelset) : Bool := (s.get l).isSome

/-- `CleanupLabels.add_label_branched_to` -/
def addLabelBranchedTo (ls : Labelset) (i : Linear.Instruction) : Labelset :=
  match i with
  | .Lgoto lbl => Labelset.add lbl ls
  | .Lcond _ _ lbl => Labelset.add lbl ls
  | .Ljumptable _ tbl => tbl.foldr Labelset.add ls
  | _ => ls

/-- `CleanupLabels.labels_branched_to` -/
def labelsBranchedTo (c : Linear.Code) : Labelset := c.foldl addLabelBranchedTo PTree.empty

/-- `CleanupLabels.remove_unused` -/
def removeUnused (bto : Labelset) (i : Linear.Instruction) (k : Linear.Code) : Linear.Code :=
  match i with
  | .Llabel lbl => if Labelset.mem lbl bto then i :: k else k
  | _ => i :: k

/-- `CleanupLabels.remove_unused_labels` -/
def removeUnusedLabels (bto : Labelset) (c : Linear.Code) : Linear.Code :=
  c.foldr (removeUnused bto) []

/-- `CleanupLabels.cleanup_labels` -/
def cleanupLabels (c : Linear.Code) : Linear.Code := removeUnusedLabels (labelsBranchedTo c) c

/-- `CleanupLabels.transf_function` -/
def transfFunction (f : Linear.Function) : Linear.Function :=
  { fn_sig := f.fn_sig, fn_stacksize := f.fn_stacksize, fn_code := cleanupLabels f.fn_code }

/-- `CleanupLabels.transf_fundef` -/
def transfFundef (f : Linear.Fundef) : Linear.Fundef := ASTFundef.transf transfFunction f

/-- `CleanupLabels.transf_program` -/
def transfProgram (p : Linear.Program) : Linear.Program := transformProgram transfFundef p

end CleanupLabels
end RiscV
end CC
