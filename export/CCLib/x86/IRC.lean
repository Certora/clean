/-
  Iterated Register Coalescing: George and Appel's graph coloring
  algorithm — port of `backend/IRC.ml` (the copy of `CCLib/backend/IRC.lean` for `CCLib/x86/`).

  The OCaml graph is a web of mutable records: each node and each move
  belongs to one of several imperative doubly-linked lists (the worklists
  of the algorithm).  Here the graph is a value of type `IRC.Graph`: nodes
  and moves are stored in arrays and referred to by their index, the
  doubly-linked lists are encoded by the `nprev`/`nnext` (`mprev`/`mnext`)
  indices, and the list heads are the first entries of the arrays (sentinel
  nodes and moves).  The algorithm runs in the state monad `IRC.GM`.  The
  order in which the nodes are first partitioned is the order of their
  creation (OCaml iterates over a hash table).

  As in OCaml, the result of `coloring` is not trusted: the allocation is
  checked by the validator `Allocation.check_function`.
-/
import CCLib.x86.XTL
import CCLib.x86.Conventions

namespace CC
namespace X86
namespace IRC

open XTL Conventions1 Conventions

/-- Floating-point infinity (OCaml `infinity`). -/
def infinity : Float := 1.0 / 0.0

/-- OCaml's `max_int` (63-bit): an infinite spill cost. -/
def maxInt : Int := 4611686018427387903

/-- `IRC.var_stats` -/
structure VarStats where
  /-- estimated cost of a spill -/
  cost : Int := 0
  /-- number of uses and defs -/
  usedefs : Nat := 0
  deriving Inhabited, Repr

/-- `IRC.nodestate` -/
inductive NodeState where
  | Colored | Initial | SimplifyWorklist | FreezeWorklist | SpillWorklist
  | CoalescedNodes | SelectStack
  deriving DecidableEq, Inhabited, Repr

/-- `IRC.movestate` -/
inductive MoveState where
  | CoalescedMoves | ConstrainedMoves | FrozenMoves | WorklistMoves | ActiveMoves
  deriving DecidableEq, Inhabited, Repr

/-- `IRC.node` (nodes are referred to by their index in `Graph.nodes`). -/
structure NodeD where
  typ : ATyp
  var : Var
  regclass : Nat
  accesses : Nat
  spillcost : Float
  adjlist : List Nat := []
  degree : Int := 0
  movelist : List Nat := []
  extraAdj : List Nat := []
  extraPref : List Nat := []
  alias : Option Nat := none
  color : Option Loc := none
  nstate : NodeState
  nprev : Nat := 0
  nnext : Nat := 0
  deriving Inhabited

/-- `IRC.move` (moves are referred to by their index in `Graph.moves`). -/
structure MoveD where
  src : Nat
  dst : Nat
  mstate : MoveState
  mprev : Nat := 0
  mnext : Nat := 0
  deriving Inhabited

/-! The sentinels (list heads) of the node and move lists. -/

def simplifyWorklist : Nat := 0
def freezeWorklist : Nat := 1
def spillWorklist : Nat := 2
def coalescedNodes : Nat := 3
def coalescedMoves : Nat := 0
def constrainedMoves : Nat := 1
def frozenMoves : Nat := 2
def worklistMoves : Nat := 3
def activeMoves : Nat := 4

/-- `IRC.graph` -/
structure Graph where
  preferredRegisters : Array (Array Mreg)
  remainingRegisters : Array (Array Mreg)
  numAvailableRegisters : Array Nat
  startPoints : Array Nat
  allocatableRegisters : List Mreg
  statsOfReg : Reg → VarStats
  varTable : Std.HashMap Var Nat := {}
  nodes : Array NodeD
  moves : Array MoveD
  adjSet : Std.HashSet (Nat × Nat) := {}

instance : Inhabited Graph :=
  ⟨{ preferredRegisters := #[], remainingRegisters := #[], numAvailableRegisters := #[],
     startPoints := #[], allocatableRegisters := [], statsOfReg := fun _ => {},
     nodes := #[], moves := #[] }⟩

/-- Computations on the interference graph. -/
abbrev GM := StateM Graph

/-! ## Register classes -/

/-- `IRC.class_of_type` -/
def classOfType : ATyp → Nat
  | .Tint | .Tlong => 0
  | .Tfloat | .Tsingle => 1
  | .Tany32 => 0
  | .Tany64 => if Archi.ptr64 then 0 else 1

/-- `IRC.class_of_reg` -/
def classOfReg (r : Mreg) : Nat := if isFloatReg r then 1 else 0

/-- `IRC.class_of_loc` -/
def classOfLoc : Loc → Nat
  | .R r => classOfReg r
  | .S _ _ ty => classOfType ty

/-- `IRC.no_spill_class` -/
def noSpillClass : Nat := 2

/-! ## Access to nodes and moves -/

def getN (i : Nat) : GM NodeD := return (← get).nodes[i]!
def modN (i : Nat) (f : NodeD → NodeD) : GM Unit :=
  modify fun g => { g with nodes := g.nodes.modify i f }
def getMv (i : Nat) : GM MoveD := return (← get).moves[i]!
def modMv (i : Nat) (f : MoveD → MoveD) : GM Unit :=
  modify fun g => { g with moves := g.moves.modify i f }
def numAvail (cls : Nat) : GM Int := return ((← get).numAvailableRegisters[cls]!)

/-! ## Doubly-linked lists of nodes (`DLinkNode`) -/

/-- `DLinkNode.insert` -/
def nInsert (n dl : Nat) : GM Unit := do
  let d ← getN dl
  let nx := d.nnext
  modN n fun x => { x with nstate := d.nstate, nnext := nx, nprev := dl }
  modN nx fun x => { x with nprev := n }
  modN dl fun x => { x with nnext := n }

/-- `DLinkNode.remove` -/
def nRemove (n : Nat) : GM Unit := do
  let x ← getN n
  modN x.nnext fun y => { y with nprev := x.nprev }
  modN x.nprev fun y => { y with nnext := x.nnext }

/-- `DLinkNode.move` -/
def nMove (n dl2 : Nat) : GM Unit := do nRemove n; nInsert n dl2

/-- `DLinkNode.notempty` -/
def nNotEmpty (dl : Nat) : GM Bool := return (← getN dl).nnext != dl

/-- `DLinkNode.pick` -/
def nPick (dl : Nat) : GM Nat := do
  let n := (← getN dl).nnext
  nRemove n
  return n

/-- The elements of a list of nodes, in order. -/
def nElements (dl : Nat) : GM (List Nat) := do
  let g ← get
  let rec go (fuel : Nat) (n : Nat) (acc : List Nat) : List Nat :=
    match fuel with
    | 0 => acc.reverse
    | fuel + 1 => if n == dl then acc.reverse else go fuel g.nodes[n]!.nnext (n :: acc)
  return go (g.nodes.size + 1) g.nodes[dl]!.nnext []

/-! ## Doubly-linked lists of moves (`DLinkMove`) -/

/-- `DLinkMove.insert` -/
def mInsert (m dl : Nat) : GM Unit := do
  let d ← getMv dl
  let nx := d.mnext
  modMv m fun x => { x with mstate := d.mstate, mnext := nx, mprev := dl }
  modMv nx fun x => { x with mprev := m }
  modMv dl fun x => { x with mnext := m }

/-- `DLinkMove.remove` -/
def mRemove (m : Nat) : GM Unit := do
  let x ← getMv m
  modMv x.mnext fun y => { y with mprev := x.mprev }
  modMv x.mprev fun y => { y with mnext := x.mnext }

/-- `DLinkMove.move` -/
def mMove (m dl2 : Nat) : GM Unit := do mRemove m; mInsert m dl2

/-- `DLinkMove.notempty` -/
def mNotEmpty (dl : Nat) : GM Bool := return (← getMv dl).mnext != dl

/-- `DLinkMove.pick` -/
def mPick (dl : Nat) : GM Nat := do
  let m := (← getMv dl).mnext
  mRemove m
  return m

/-! ## Initialization -/

/-- A sentinel node (the head of an empty list). -/
def sentinelNode (i : Nat) (st : NodeState) : NodeD :=
  { typ := .Tint, var := .V .xH .Tint, regclass := 0, accesses := 0, spillcost := 0,
    nstate := st, nprev := i, nnext := i }

/-- A sentinel move. -/
def sentinelMove (i : Nat) (st : MoveState) : MoveD :=
  { src := 0, dst := 0, mstate := st, mprev := i, mnext := i }

/-- `IRC.init` (`CPragmas.reserved_registers` is empty). -/
def init (win64 : Bool) (costs : Reg → VarStats) : Graph :=
  let aregs := allocatableRegisters win64 ()
  let ip := aregs.preferred_int_regs
  let fp := aregs.preferred_float_regs
  let ir := aregs.remaining_int_regs
  let fr := aregs.remaining_float_regs
  { preferredRegisters := #[ip.toArray, fp.toArray, #[]]
    remainingRegisters := #[ir.toArray, fr.toArray, #[]]
    numAvailableRegisters := #[ip.length + ir.length, fp.length + fr.length, 0]
    startPoints := #[0, 0, 0]
    allocatableRegisters := ip ++ ir ++ fp ++ fr
    statsOfReg := costs
    nodes := #[sentinelNode 0 .SimplifyWorklist, sentinelNode 1 .FreezeWorklist,
               sentinelNode 2 .SpillWorklist, sentinelNode 3 .CoalescedNodes]
    moves := #[sentinelMove 0 .CoalescedMoves, sentinelMove 1 .ConstrainedMoves,
               sentinelMove 2 .FrozenMoves, sentinelMove 3 .WorklistMoves,
               sentinelMove 4 .ActiveMoves] }

/-! ## Nodes corresponding to XTL variables -/

/-- `IRC.weightedSpillCost` -/
def weightedSpillCost (st : VarStats) : Float :=
  if st.cost < maxInt then Float.ofInt st.cost else infinity

/-- `IRC.newNodeOfReg` -/
def newNodeOfReg (g : Graph) (r : Reg) (ty : ATyp) : NodeD :=
  let st := g.statsOfReg r
  { typ := ty, var := .V r ty
    regclass := if st.cost ≥ 0 then classOfType ty else noSpillClass
    accesses := st.usedefs, spillcost := weightedSpillCost st
    degree := if st.cost ≥ 0 then 0 else 1
    nstate := .Initial }

/-- `IRC.newNodeOfLoc` -/
def newNodeOfLoc (l : Loc) : NodeD :=
  { typ := l.type, var := .L l, regclass := classOfLoc l, accesses := 0, spillcost := 0
    color := some l, nstate := .Colored }

/-- `IRC.nodeOfVar` -/
def nodeOfVar (v : Var) : GM Nat := do
  let g ← get
  match g.varTable.get? v with
  | some n => return n
  | none =>
    let nd := match v with
      | .V r ty => newNodeOfReg g r ty
      | .L l => newNodeOfLoc l
    let n := g.nodes.size
    set { g with nodes := g.nodes.push nd, varTable := g.varTable.insert v n }
    return n

/-- The key of an edge in `adjSet`. -/
def edgeKey (i1 i2 : Nat) : Nat × Nat := if i1 < i2 then (i1, i2) else (i2, i1)

/-- `IRC.interfere` -/
def interfere (n1 n2 : Nat) : GM Bool := return (← get).adjSet.contains (edgeKey n1 n2)

/-- `IRC.recordInterf` -/
def recordInterf (n1 n2 : Nat) : GM Unit := do
  let x1 ← getN n1
  let x2 ← getN n2
  match x2.color with
  | none | some (.R _) =>
    if x1.regclass == x2.regclass then
      modN n1 fun x => { x with adjlist := n2 :: x.adjlist, degree := 1 + x.degree }
    else
      modN n1 fun x => { x with extraAdj := n2 :: x.extraAdj }
  | some (.S ..) => modN n1 fun x => { x with extraAdj := n2 :: x.extraAdj }

/-- `IRC.addEdge` (OCaml asserts that the nodes differ; here an edge from a
    node to itself is ignored). -/
def addEdge (n1 n2 : Nat) : GM Unit := do
  if n1 == n2 then return
  if !(← interfere n1 n2) then
    modify fun g => { g with adjSet := g.adjSet.insert (edgeKey n1 n2) }
    if (← getN n1).nstate != .Colored then recordInterf n1 n2
    if (← getN n2).nstate != .Colored then recordInterf n2 n1

/-- `IRC.recordMove` -/
def recordMove (n1 n2 : Nat) : GM Unit := do
  let m := (← get).moves.size
  modify fun g => { g with moves := g.moves.push { src := n1, dst := n2, mstate := .WorklistMoves } }
  modN n1 fun x => { x with movelist := m :: x.movelist }
  modN n2 fun x => { x with movelist := m :: x.movelist }
  mInsert m worklistMoves

/-- A move that is not in any list (`mstate = FrozenMoves`). -/
def newFrozenMove (n1 n2 : Nat) : GM Nat := do
  let m := (← get).moves.size
  modify fun g => { g with moves := g.moves.push { src := n1, dst := n2, mstate := .FrozenMoves } }
  return m

/-- `IRC.recordExtraPref` -/
def recordExtraPref (n1 n2 : Nat) : GM Unit := do
  let m ← newFrozenMove n1 n2
  modN n1 fun x => { x with extraPref := m :: x.extraPref }

/-- `IRC.recordExtraPref2` -/
def recordExtraPref2 (n1 n2 : Nat) : GM Unit := do
  let m ← newFrozenMove n1 n2
  modN n1 fun x => { x with extraPref := m :: x.extraPref }
  modN n2 fun x => { x with extraPref := m :: x.extraPref }

/-- `IRC.addMovePref` -/
def addMovePref (n1 n2 : Nat) : GM Unit := do
  let x1 ← getN n1
  let x2 ← getN n2
  let aregs := (← get).allocatableRegisters
  match x1.color, x2.color with
  | none, none =>
    if x1.regclass == x2.regclass then recordMove n1 n2 else recordExtraPref2 n1 n2
  | some (.R mr1), none => if aregs.contains mr1 then recordMove n1 n2
  | none, some (.R mr2) => if aregs.contains mr2 then recordMove n1 n2
  | some (.S ..), none => recordExtraPref n2 n1
  | none, some (.S ..) => recordExtraPref n1 n2
  | _, _ => pure ()

/-- `IRC.iterAdjacent` -/
def iterAdjacent (f : Nat → GM Unit) (n : Nat) : GM Unit := do
  for a in (← getN n).adjlist do
    match (← getN a).nstate with
    | .SelectStack | .CoalescedNodes => pure ()
    | _ => f a

/-- The relevant adjacent nodes of a node (for read-only scans). -/
def adjacent (n : Nat) : GM (List Nat) := do
  let g ← get
  return g.nodes[n]!.adjlist.filter fun a =>
    match g.nodes[a]!.nstate with
    | .SelectStack | .CoalescedNodes => false
    | _ => true

/-- `IRC.moveIsActiveOrWorklist` -/
def moveIsActiveOrWorklist (m : Nat) : GM Bool := do
  match (← getMv m).mstate with
  | .ActiveMoves | .WorklistMoves => return true
  | _ => return false

/-- `IRC.nodeMoves` -/
def nodeMoves (n : Nat) : GM (List Nat) := do
  (← getN n).movelist.filterM moveIsActiveOrWorklist

/-- `IRC.moveRelated` -/
def moveRelated (n : Nat) : GM Bool := do
  (← getN n).movelist.anyM moveIsActiveOrWorklist

/-- `IRC.initialNodePartition` -/
def initialNodePartition : GM Unit := do
  let size := (← get).nodes.size
  for n in [4:size] do
    let x ← getN n
    if x.nstate == .Initial then
      let k ← numAvail x.regclass
      if x.degree ≥ k then nInsert n spillWorklist
      else if ← moveRelated n then nInsert n freezeWorklist
      else nInsert n simplifyWorklist

/-- `IRC.enableMoves` -/
def enableMoves (n : Nat) : GM Unit := do
  for m in ← nodeMoves n do
    if (← getMv m).mstate == .ActiveMoves then mMove m worklistMoves

/-- `IRC.decrementDegree` -/
def decrementDegree (n : Nat) : GM Unit := do
  let x ← getN n
  let k ← numAvail x.regclass
  let d := x.degree
  modN n fun x => { x with degree := d - 1 }
  if d == k then
    enableMoves n
    iterAdjacent enableMoves n
    if ← moveRelated n then nMove n freezeWorklist else nMove n simplifyWorklist

/-- `IRC.combineEdge` -/
def combineEdge (n1 n2 : Nat) : GM Unit := do
  if n1 == n2 then return
  if ← interfere n1 n2 then
    decrementDegree n2
  else
    modify fun g => { g with adjSet := g.adjSet.insert (edgeKey n1 n2) }
    if (← getN n1).nstate != .Colored then
      modN n1 fun x => { x with adjlist := n2 :: x.adjlist, degree := 1 + x.degree }
    if (← getN n2).nstate != .Colored then
      modN n2 fun x => { x with adjlist := n1 :: x.adjlist }

/-- `IRC.simplify` -/
def simplify : GM Nat := do
  let n ← nPick simplifyWorklist
  modN n fun x => { x with nstate := .SelectStack }
  iterAdjacent decrementDegree n
  return n

/-- `IRC.canCoalesceBriggs` -/
def canCoalesceBriggs (u v : Nat) : GM Bool := do
  let k ← numAvail (← getN u).regclass
  let mut seen : Std.HashSet Nat := {}
  let mut c : Int := 0
  for (other, lst) in [(v, ← adjacent u), (u, ← adjacent v)] do
    for n in lst do
      if !seen.contains n then
        seen := seen.insert n
        let x ← getN n
        let degAfter := if ← interfere n other then x.degree - 1 else x.degree
        if degAfter ≥ k || x.nstate == .Colored then c := c + 1
  return c < k

/-- `IRC.canCoalesceGeorge` -/
def canCoalesceGeorge (u v : Nat) : GM Bool := do
  let xu ← getN u
  let k ← numAvail xu.regclass
  for t in ← adjacent v do
    let xt ← getN t
    let ok ← if xt.nstate == .Colored then
        pure (xu.nstate == .Colored || (← interfere t u))
      else
        pure (xt.degree < k || (← interfere t u))
    if !ok then return false
  return true

/-- `IRC.thresholdGeorge` -/
def thresholdGeorge : Nat := 3

/-- `IRC.canCoalesce` -/
def canCoalesce (u v : Nat) : GM Bool := do
  let xu ← getN u
  let xv ← getN v
  if xu.nstate == .Colored then canCoalesceGeorge u v
  else if ← canCoalesceBriggs u v then return true
  else if xu.spillcost < infinity && xv.spillcost < infinity then
    if xv.accesses ≤ thresholdGeorge && (← canCoalesceGeorge u v) then return true
    else return xu.accesses ≤ thresholdGeorge && (← canCoalesceGeorge v u)
  else return false

/-- `IRC.addWorkList` -/
def addWorkList (u : Nat) : GM Unit := do
  let x ← getN u
  if x.nstate != .Colored && x.degree < (← numAvail x.regclass) && !(← moveRelated u) then
    nMove u simplifyWorklist

/-- `IRC.getAlias` -/
def getAlias (n : Nat) : GM Nat := do
  let g ← get
  let rec go (fuel n : Nat) : Nat :=
    match fuel with
    | 0 => n
    | fuel + 1 => match g.nodes[n]!.alias with
      | none => n
      | some n' => go fuel n'
  return go g.nodes.size n

/-- `IRC.combine` -/
def combine (u v : Nat) : GM Unit := do
  -- `v` leaves the freeze or the spill worklist
  nMove v coalescedNodes
  modN v fun x => { x with alias := some u }
  let xv ← getN v
  modN u fun x => { x with movelist := xv.movelist.reverse ++ x.movelist
                           spillcost := x.spillcost + xv.spillcost }
  iterAdjacent (combineEdge u) v
  if (← getN u).nstate != .Colored then
    modN u fun x => { x with extraAdj := xv.extraAdj.reverse ++ x.extraAdj
                             extraPref := xv.extraPref.reverse ++ x.extraPref }
  enableMoves v
  let xu ← getN u
  if xu.degree ≥ (← numAvail xu.regclass) && xu.nstate == .FreezeWorklist then
    nMove u spillWorklist

/-- `IRC.coalesce` -/
def coalesce : GM Unit := do
  let m ← mPick worklistMoves
  let mv ← getMv m
  let x ← getAlias mv.src
  let y ← getAlias mv.dst
  let (u, v) := if (← getN y).nstate == .Colored then (y, x) else (x, y)
  if u == v then
    mInsert m coalescedMoves
    addWorkList u
  else if (← getN v).nstate == .Colored || (← interfere u v) then
    mInsert m constrainedMoves
    addWorkList u
    addWorkList v
  else if ← canCoalesce u v then
    mInsert m coalescedMoves
    combine u v
    addWorkList u
  else
    mInsert m activeMoves

/-- `IRC.freezeMoves` -/
def freezeMoves (u : Nat) : GM Unit := do
  let u' ← getAlias u
  for m in ← nodeMoves u do
    let mv ← getMv m
    let y ← getAlias mv.src
    let v ← if y == u' then getAlias mv.dst else pure y
    mMove m frozenMoves
    let xv ← getN v
    if !(← moveRelated v) && xv.degree < (← numAvail xv.regclass) && xv.nstate != .Colored then
      nMove v simplifyWorklist

/-- `IRC.freeze` -/
def freeze : GM Unit := do
  let u ← nPick freezeWorklist
  nInsert u simplifyWorklist
  freezeMoves u

/-- `IRC.selectSpill`: spill the node of minimal cost (function `h_0` of
    Bernstein et al.: spill cost divided by the square of the degree). -/
def selectSpill : GM Nat := do
  let mut best : Option Nat := none
  let mut bestCost : Float := infinity
  for n in ← nElements spillWorklist do
    let x ← getN n
    let deg := Float.ofInt x.degree
    let deg2 := deg * deg
    if x.spillcost ≤ bestCost * deg2 then
      best := some n
      bestCost := x.spillcost / deg2
  -- OCaml asserts that a node was found
  let n ← match best with
    | some n => pure n
    | none => pure (← getN spillWorklist).nnext
  nRemove n
  freezeMoves n
  modN n fun x => { x with nstate := .SelectStack }
  iterAdjacent decrementDegree n
  return n

/-- `IRC.nodeOrder`: the order in which the nodes are colored. -/
partial def nodeOrder (stack : List Nat) : GM (List Nat) := do
  if ← nNotEmpty simplifyWorklist then
    let n ← simplify
    nodeOrder (n :: stack)
  else if ← mNotEmpty worklistMoves then
    coalesce
    nodeOrder stack
  else if ← nNotEmpty freezeWorklist then
    freeze
    nodeOrder stack
  else if ← nNotEmpty spillWorklist then
    let n ← selectSpill
    nodeOrder (n :: stack)
  else
    return stack

/-! ## Assigning colors -/

/-- `IRC.find_reg`: a register of the class that is not in `conflicts`,
    trying first the preferred registers (from a rotating start point), then
    the remaining ones. -/
def findReg (conflicts : List Mreg) (regclass : Nat) : GM (Option Loc) := do
  let g ← get
  let find (avail : Array Mreg) (curr last : Nat) : Option Loc :=
    ((List.range (last - curr)).map (· + curr)).findSome? fun i =>
      let r := avail[i]!
      if conflicts.contains r then none else some (.R r)
  let preferred := g.preferredRegisters[regclass]!
  let remaining := g.remainingRegisters[regclass]!
  let start := g.startPoints[regclass]!
  let next := if start + 1 < preferred.size then start + 1 else 0
  match find preferred start preferred.size with
  | some res =>
    set { g with startPoints := g.startPoints.set! regclass next }
    return some res
  | none =>
    match find preferred 0 start with
    | some res =>
      set { g with startPoints := g.startPoints.set! regclass next }
      return some res
    | none => return find remaining 0 remaining.size

/-- `IRC.reuse_slot`: aggressive coalescing of stack slots. -/
def reuseSlot (conflicts : List Loc) (n : Nat) (mvlist : List Nat) : GM (Option Loc) := do
  for m in mvlist do
    let mv ← getMv m
    let src ← getAlias mv.src
    let dst ← getAlias mv.dst
    let other := if n == src then some dst else if n == dst then some src else none
    match other with
    | some n' =>
      match (← getN n').color with
      | some l@(.S .Local _ _) =>
        if conflicts.all (fun c => decide (Loc.diff l c)) then return some l
      | _ => pure ()
    | none => pure ()
  return none

/-- `IRC.align` -/
def align (a b : Int) : Int := (a + b - 1) / b * b

/-- `IRC.find_slot`: the lowest `Local` slot that does not conflict. -/
def findSlot (conflicts : List Loc) (typ : ATyp) : Loc := Id.run do
  let sz := typesize typ
  let al := typealign typ
  let ofsOf : Loc → Int := fun l => match l with | .S _ ofs _ => ofs | _ => 0
  let sorted := conflicts.mergeSort (fun a b => ofsOf a ≤ ofsOf b)
  let mut curr : Int := 0
  for l in sorted do
    match l with
    | .S .Local ofs typ' =>
      if curr + sz ≤ ofs then return .S .Local curr typ
      let ofs' := align (ofs + typesize typ') al
      curr := if ofs' ≤ curr then curr else ofs'
    | _ => pure ()
  return .S .Local curr typ

/-- `IRC.assign_color` -/
def assignColor (n : Nat) : GM Unit := do
  let x ← getN n
  let colorOf (m : Nat) : GM (Option Loc) := do return (← getN (← getAlias m)).color
  let mut regConflicts : List Mreg := []
  for a in x.adjlist do
    if let some (.R r) ← colorOf a then regConflicts := r :: regConflicts
  match ← findReg regConflicts x.regclass with
  | some loc => modN n fun x => { x with color := some loc }
  | none =>
    let mut slotConflicts : List Loc := []
    for a in x.adjlist ++ x.extraAdj do
      if let some l@(.S ..) ← colorOf a then slotConflicts := l :: slotConflicts
    match ← reuseSlot slotConflicts n (x.extraPref ++ x.movelist) with
    | some loc => modN n fun x => { x with color := some loc }
    | none => modN n fun x => { x with color := some (findSlot slotConflicts x.typ) }

/-- `IRC.location_of_var` -/
def locationOfVar (g : Graph) (v : Var) : Loc :=
  match v with
  | .L l => l
  | .V _ ty =>
    match g.varTable.get? v with
    | some n =>
      let n' := Id.run ((getAlias n).run' g)
      match g.nodes[n']!.color with
      | some l => l
      | none => .R dummyIntReg  -- OCaml: `assert false`
    | none => if classOfType ty == 1 then .R dummyFloatReg else .R dummyIntReg

/-! ## The exported interface -/

/-- `IRC.add_interf` -/
def addInterf (v1 v2 : Var) : GM Unit := do
  let n1 ← nodeOfVar v1
  let n2 ← nodeOfVar v2
  addEdge n1 n2

/-- `IRC.add_pref` -/
def addPref (v1 v2 : Var) : GM Unit := do
  let n1 ← nodeOfVar v1
  let n2 ← nodeOfVar v2
  addMovePref n1 n2

/-- `IRC.coloring`: color the graph; the result maps every variable to a
    location. -/
def coloring : GM (Var → Loc) := do
  initialNodePartition
  for n in ← nodeOrder [] do assignColor n
  return locationOfVar (← get)

end IRC
end X86
end CC
