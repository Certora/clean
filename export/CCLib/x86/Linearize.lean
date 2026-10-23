/-
  [x86-64 instance of `CCLib/backend/Linearize.lean`: the same development, in
  namespace `CC.X86`, over the x86-64 operators, registers and conventions.]

  Linearization of the LTL control-flow graph into Linear code — port of
  `backend/Linearize.v` (`reachable`, `nodeset_of_list`,
  `check_reachable`, `enumerate`, `starts_with`, `add_branch`,
  `linearize_block`, `linearize_node`, `linearize_body`,
  `transf_function`, `transf_fundef`, `transf_program`), together with a
  Lean version of the untrusted OCaml heuristic `Linearizeaux.enumerate_aux`.

  Differences from Rocq:
  * `enumerate_aux` is a Rocq `Parameter` implemented in OCaml; here the
    translation takes it as an explicit argument `enumAux`.
    `Linearize.enumerateAuxDefault` is a Lean transcription of
    `Linearizeaux.ml` (join points, basic blocks, flattening in decreasing
    order of their smallest node), with explicit fuel for its traversals.
  * `Nodeset` (an AVL set) is a `PTree Unit`.
-/
import CCLib.x86.LTL
import CCLib.x86.Linear
import CCLib.backend.Kildall
import CCLib.x86.Tailcall

namespace CC
namespace X86
namespace Linearize

open LTL

/-- `Linearize.reachable_aux` (the solver `DS` is `Dataflow_Solver(LBoolean)(NodeSetForward)`). -/
def reachableAux (f : LTL.Function) : Option (PMap Bool) :=
  Kildall.fixpoint (L := Bool) (NS := NodeSetForward) f.fn_code successorsBlock (fun _ r => r)
    f.fn_entrypoint true

/-- `Linearize.reachable` -/
def reachable (f : LTL.Function) : PMap Bool :=
  match reachableAux f with
  | none => PMap.init true
  | some rs => rs

/-- `Linearize.Nodeset` -/
abbrev Nodeset := PTree Unit

def Nodeset.mem (n : Positive) (s : Nodeset) : Bool := (s.get n).isSome

/-- `Linearize.nodeset_of_list` -/
def nodesetOfList : List LTL.Node → Nodeset → Res Nodeset
  | [], s => .OK s
  | hd :: tl, s =>
      if Nodeset.mem hd s then .Error "Linearize: duplicates in enumeration"
      else nodesetOfList tl (s.set hd ())

/-- `Linearize.check_reachable_aux` -/
def checkReachableAux (reach : PMap Bool) (s : Nodeset) (ok : Bool) (pc : LTL.Node) (_bb : Bblock) :
    Bool :=
  if reach.get pc then ok && Nodeset.mem pc s else ok

/-- `Linearize.check_reachable` -/
def checkReachable (f : LTL.Function) (reach : PMap Bool) (s : Nodeset) : Bool :=
  PTree.fold (checkReachableAux reach s) f.fn_code true

/-! ### The OCaml heuristic `Linearizeaux.enumerate_aux` -/

/-- `Linearizeaux.join_points`: reachable nodes with more than one predecessor. -/
def joinPoints (f : LTL.Function) : Nodeset :=
  let rec go : Nat → List LTL.Node → Nodeset → Nodeset → Nodeset
    | 0, _, _, twice => twice
    | _ + 1, [], _, twice => twice
    | fuel + 1, pc :: stack, reached, twice =>
        if Nodeset.mem pc reached then
          go fuel stack reached (twice.set pc ())
        else
          let succs := match f.fn_code.get pc with
            | none => []
            | some b => successorsBlock b
          go fuel (succs ++ stack) (reached.set pc ()) twice
  go PrimIter.numIterations [f.fn_entrypoint] PTree.empty PTree.empty

/-- Follow a chain of `Lbranch`es from `pc`, returning the block (in order),
    its smallest node, and the nodes that start new blocks
    (`Linearizeaux.in_block` / `next_in_block`). -/
def inBlock (f : LTL.Function) (joins : Nodeset) :
    Nat → List LTL.Node → Nat → LTL.Node → List LTL.Node × Nat × List LTL.Node
  | 0, blk, minpc, _ => (blk.reverse, minpc, [])
  | fuel + 1, blk, minpc, pc =>
      let blk := pc :: blk
      let minpc := min pc.toNat minpc
      match f.fn_code.get pc with
      | none => (blk.reverse, minpc, [])
      | some b =>
          let rec doInstrs : Bblock → List LTL.Node × Nat × List LTL.Node
            | [] => (blk.reverse, minpc, [])
            | .Lbranch s :: _ =>
                if Nodeset.mem s joins then (blk.reverse, minpc, [s])
                else inBlock f joins fuel blk minpc s
            | .Ltailcall _ _ :: _ => (blk.reverse, minpc, [])
            | .Lcond _ _ ifso ifnot :: _ => (blk.reverse, minpc, [ifso, ifnot])
            | .Ljumptable _ tbl :: _ => (blk.reverse, minpc, tbl)
            | .Lreturn :: _ => (blk.reverse, minpc, [])
            | _ :: b' => doInstrs b'
          doInstrs b

/-- `Linearizeaux.basic_blocks`: the reachable basic blocks, each with its
    smallest node. -/
def basicBlocks (f : LTL.Function) (joins : Nodeset) : List (Nat × List LTL.Node) :=
  let rec go : Nat → List LTL.Node → Nodeset → List (Nat × List LTL.Node) →
      List (Nat × List LTL.Node)
    | 0, _, _, blocks => blocks
    | _ + 1, [], _, blocks => blocks
    | fuel + 1, pc :: work, visited, blocks =>
        if Nodeset.mem pc visited then go fuel work visited blocks
        else
          let (blk, minpc, starts) :=
            inBlock f joins PrimIter.numIterations [] PrimIter.numIterations pc
          go fuel (starts ++ work) (visited.set pc ()) ((minpc, blk) :: blocks)
  go PrimIter.numIterations [f.fn_entrypoint] PTree.empty []

/-- Insertion in a list sorted by decreasing first component. -/
def insertByMinpc (x : Nat × List LTL.Node) : List (Nat × List LTL.Node) → List (Nat × List LTL.Node)
  | [] => [x]
  | y :: l => if x.1 ≥ y.1 then x :: y :: l else y :: insertByMinpc x l

/-- `Linearizeaux.flatten_blocks`: concatenation in decreasing order of the
    smallest node. -/
def flattenBlocks (blks : List (Nat × List LTL.Node)) : List LTL.Node :=
  ((blks.foldr insertByMinpc []).map Prod.snd).flatten

/-- `Linearizeaux.enumerate_aux` -/
def enumerateAuxDefault (f : LTL.Function) (_reach : PMap Bool) : List LTL.Node :=
  flattenBlocks (basicBlocks f (joinPoints f))

/-! ### Validation and translation -/

section TRANSF
variable (enumAux : LTL.Function → PMap Bool → List LTL.Node)

/-- `Linearize.enumerate` -/
def enumerate (f : LTL.Function) : Res (List LTL.Node) :=
  let reach := reachable f
  let enum := enumAux f reach
  match nodesetOfList enum PTree.empty with
  | .Error m => .Error m
  | .OK s =>
      if checkReachable f reach s then .OK enum
      else .Error "Linearize: wrong enumeration"

/-- `Linearize.starts_with` -/
def startsWith (lbl : Linear.Label) : Linear.Code → Bool
  | .Llabel lbl' :: k' => if lbl = lbl' then true else startsWith lbl k'
  | _ => false

/-- `Linearize.add_branch` -/
def addBranch (s : Linear.Label) (k : Linear.Code) : Linear.Code :=
  if startsWith s k then k else .Lgoto s :: k

/-- `Linearize.linearize_block` -/
def linearizeBlock : Bblock → Linear.Code → Linear.Code
  | [], k => k
  | .Lop op args res :: b', k => .Lop op args res :: linearizeBlock b' k
  | .Lload chunk addr args dst :: b', k => .Lload chunk addr args dst :: linearizeBlock b' k
  | .Lgetstack sl ofs ty dst :: b', k => .Lgetstack sl ofs ty dst :: linearizeBlock b' k
  | .Lsetstack src sl ofs ty :: b', k => .Lsetstack src sl ofs ty :: linearizeBlock b' k
  | .Lstore chunk addr args src :: b', k => .Lstore chunk addr args src :: linearizeBlock b' k
  | .Lcall sig ros :: b', k => .Lcall sig ros :: linearizeBlock b' k
  | .Ltailcall sig ros :: _, k => .Ltailcall sig ros :: k
  | .Lbuiltin ef args res :: b', k => .Lbuiltin ef args res :: linearizeBlock b' k
  | .Lbranch s :: _, k => addBranch s k
  | .Lcond cond args s1 s2 :: _, k =>
      if startsWith s1 k then .Lcond (Op.negateCondition cond) args s2 :: addBranch s1 k
      else .Lcond cond args s1 :: addBranch s2 k
  | .Ljumptable arg tbl :: _, k => .Ljumptable arg tbl :: k
  | .Lreturn :: _, k => .Lreturn :: k

/-- `Linearize.linearize_node` -/
def linearizeNode (f : LTL.Function) (pc : LTL.Node) (k : Linear.Code) : Linear.Code :=
  match f.fn_code.get pc with
  | none => k
  | some b => .Llabel pc :: linearizeBlock b k

/-- `Linearize.linearize_body` -/
def linearizeBody (f : LTL.Function) (enum : List LTL.Node) : Linear.Code :=
  enum.foldr (linearizeNode f) []

/-- `Linearize.transf_function` -/
def transfFunction (f : LTL.Function) : Res Linear.Function :=
  match enumerate enumAux f with
  | .Error m => .Error m
  | .OK enum =>
      .OK { fn_sig := f.fn_sig, fn_stacksize := f.fn_stacksize,
            fn_code := addBranch f.fn_entrypoint (linearizeBody f enum) }

/-- `Linearize.transf_fundef` -/
def transfFundef (f : LTL.Fundef) : Res Linear.Fundef :=
  ASTFundef.transfPartial (transfFunction enumAux) f

/-- `Linearize.transf_program` -/
def transfProgram (p : LTL.Program) : Res Linear.Program :=
  transformPartialProgram (transfFundef enumAux) p

end TRANSF

end Linearize
end X86
end CC
