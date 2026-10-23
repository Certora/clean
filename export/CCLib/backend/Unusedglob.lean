/-
  Elimination of unreferenced static definitions — port of
  `backend/Unusedglob.v` (an RTL → RTL pass), whole file: `workset`,
  `add_workset`, `addlist_workset`, `ref_instruction`,
  `add_ref_instruction`, `add_ref_function`, `add_ref_init_data`,
  `add_ref_globvar`, `prog_map`, `add_ref_definition`, `initial_workset`,
  `iter_step`, `used_globals`, `filter_globdefs`, `global_defined`,
  `transform_program`.

  Differences from Rocq: the identifier set `IS` (an AVL set of positives)
  is a duplicate-free list of identifiers.
-/
import CCLib.backend.RTL
import CCLib.backend.Kildall

namespace CC
namespace Unusedglob

open RTL

/-- `Unusedglob.IS.t`, as a duplicate-free list of identifiers. -/
abbrev IS := List Ident

namespace IS
def empty : IS := []
def mem (x : Ident) (s : IS) : Bool := s.contains x
def add (x : Ident) (s : IS) : IS := if mem x s then s else x :: s
def remove (x : Ident) (s : IS) : IS := s.filter (fun y => y != x)
def forAll (p : Ident → Bool) (s : IS) : Bool := s.all p
end IS

/-- `Unusedglob.workset` -/
structure Workset where
  w_seen : IS
  w_todo : List Ident

/-- `Unusedglob.add_workset` -/
def addWorkset (id : Ident) (w : Workset) : Workset :=
  if IS.mem id w.w_seen then w else { w_seen := IS.add id w.w_seen, w_todo := id :: w.w_todo }

/-- `Unusedglob.addlist_workset` -/
def addlistWorkset : List Ident → Workset → Workset
  | [], w => w
  | id :: l', w => addlistWorkset l' (addWorkset id w)

/-- `Unusedglob.ref_instruction` -/
def refInstruction (i : Instruction) : List Ident :=
  match i with
  | .Inop _ => []
  | .Iop op _ _ _ => Op.globalsOperation op
  | .Iload _ addr _ _ _ => Op.globalsAddressing addr
  | .Istore _ addr _ _ _ => Op.globalsAddressing addr
  | .Icall _ (.inl _) _ _ _ => []
  | .Icall _ (.inr id) _ _ _ => [id]
  | .Itailcall _ (.inl _) _ => []
  | .Itailcall _ (.inr id) _ => [id]
  | .Ibuiltin _ args _ _ => BuiltinArg.globalsList args
  | .Icond _ _ _ _ => []
  | .Ijumptable _ _ => []
  | .Ireturn _ => []

/-- `Unusedglob.add_ref_instruction` -/
def addRefInstruction (w : Workset) (_pc : Node) (i : Instruction) : Workset :=
  addlistWorkset (refInstruction i) w

/-- `Unusedglob.add_ref_function` -/
def addRefFunction (f : RTL.Function) (w : Workset) : Workset :=
  PTree.fold addRefInstruction f.fn_code w

/-- `Unusedglob.add_ref_init_data` -/
def addRefInitData (w : Workset) (i : InitData) : Workset :=
  match i with
  | .Init_addrof id _ => addWorkset id w
  | _ => w

/-- `Unusedglob.add_ref_globvar` -/
def addRefGlobvar (gv : GlobVar Unit) (w : Workset) : Workset :=
  gv.gvar_init.foldl addRefInitData w

/-- `Unusedglob.prog_map` -/
abbrev ProgMap := PTree (GlobDef Fundef Unit)

/-- `Unusedglob.add_ref_definition` -/
def addRefDefinition (pm : ProgMap) (id : Ident) (w : Workset) : Workset :=
  match pm.get id with
  | none => w
  | some (.Gfun (.Internal f)) => addRefFunction f w
  | some (.Gfun (.External _)) => w
  | some (.Gvar gv) => addRefGlobvar gv w

/-- `Unusedglob.initial_workset` -/
def initialWorkset (p : RTL.Program) : Workset :=
  addWorkset p.prog_main
    (p.prog_public.foldl (fun w id => addWorkset id w) { w_seen := IS.empty, w_todo := [] })

/-- `Unusedglob.iter_step` -/
def iterStep (pm : ProgMap) (w : Workset) : IS ⊕ Workset :=
  match w.w_todo with
  | [] => .inl w.w_seen
  | id :: rem => .inr (addRefDefinition pm id { w_seen := w.w_seen, w_todo := rem })

/-- `Unusedglob.used_globals` -/
def usedGlobals (p : RTL.Program) (pm : ProgMap) : Option IS :=
  PrimIter.iterate (iterStep pm) (initialWorkset p)

/-- `Unusedglob.filter_globdefs` -/
def filterGlobdefs : IS → List (Ident × GlobDef Fundef Unit) → List (Ident × GlobDef Fundef Unit) →
    List (Ident × GlobDef Fundef Unit)
  | _, accu, [] => accu
  | used, accu, (id, gd) :: defs' =>
      if IS.mem id used then filterGlobdefs (IS.remove id used) ((id, gd) :: accu) defs'
      else filterGlobdefs used accu defs'

/-- `Unusedglob.global_defined` -/
def globalDefined (p : RTL.Program) (pm : ProgMap) (id : Ident) : Bool :=
  match pm.get id with
  | some _ => true
  | none => decide (id = p.prog_main)

/-- `Unusedglob.transform_program` -/
def transformProgram (p : RTL.Program) : Res RTL.Program :=
  let pm := p.defmap
  match usedGlobals p pm with
  | none => .Error "Unusedglob: analysis failed"
  | some used =>
      if IS.forAll (globalDefined p pm) used then
        .OK { prog_defs := filterGlobdefs used [] p.prog_defs.reverse,
              prog_public := p.prog_public, prog_main := p.prog_main }
      else .Error "Unusedglob: reference to undefined global"

end Unusedglob
end CC
