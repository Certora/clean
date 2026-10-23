/-
  The XTL intermediate language for register allocation — port of
  `backend/XTL.ml` (the copy of `CCLib/backend/XTL.lean` for `CCLib/x86/`).

  XTL is RTL where the operands are *variables*: either pseudo-registers
  with their types (`V r ty`) or fixed locations (`L l`).  It is used by the
  register allocator (`Regalloc.lean`, `IRC.lean`).

  The OCaml module keeps the generator of fresh registers (`next_temp`,
  `twin_table`) in global references.  Here it is the state of the monad
  `XTL.TempM`.  Sets of variables (`VSet`) are hash sets.  The generic
  transformation of extended basic blocks (`transform_basic_blocks`) is a
  `partial` function, like the OCaml recursion it ports.
-/
import Std.Data.HashSet
import Std.Data.HashMap
import CCLib.x86.RTL
import CCLib.x86.Locations

namespace CC
namespace X86
namespace XTL

open Op

deriving instance Hashable for Positive
deriving instance Hashable for ATyp
deriving instance Hashable for Mreg
deriving instance Hashable for Slot
deriving instance Hashable for Loc

/-- `XTL.var` -/
inductive Var where
  | V (r : Reg) (ty : ATyp)
  | L (l : Loc)
  deriving DecidableEq, Hashable, Repr, Inhabited

/-- `XTL.node` -/
abbrev Node := Positive

/-- `XTL.instruction` -/
inductive Instruction where
  | Xmove (src dst : Var)
  | Xreload (src dst : Var)
  | Xspill (src dst : Var)
  | Xparmove (srcs dsts : List Var) (itmp ftmp : Var)
  | Xop (op : Operation) (args : List Var) (res : Var)
  | Xload (chunk : Chunk) (addr : Addressing) (args : List Var) (dst : Var)
  | Xstore (chunk : Chunk) (addr : Addressing) (args : List Var) (src : Var)
  | Xcall (sg : Signature) (ros : Sum Var Ident) (args res : List Var)
  | Xtailcall (sg : Signature) (ros : Sum Var Ident) (args : List Var)
  | Xbuiltin (ef : ExtFun) (args : List (BuiltinArg Var)) (res : BuiltinRes Var)
  | Xbranch (s : Node)
  | Xcond (cond : Condition) (args : List Var) (s1 s2 : Node)
  | Xjumptable (arg : Var) (tbl : List Node)
  | Xreturn (args : List Var)
  deriving Inhabited

/-- `XTL.block`: terminated by one of `Xbranch`, `Xcond`, `Xjumptable`,
    `Xtailcall` or `Xreturn`. -/
abbrev Block := List Instruction

/-- `XTL.code` -/
abbrev Code := PTree Block

/-- `XTL.xfunction` -/
structure XFunction where
  fn_sig : Signature
  fn_stacksize : Z
  fn_code : Code
  fn_entrypoint : Node

/-- `XTL.typeof` -/
def typeof : Var → ATyp
  | .V _ ty => ty
  | .L l => l.type

/-! ## Constructors for type `var` -/

/-- `XTL.vloc` -/
def vloc (l : Loc) : Var := .L l
/-- `XTL.vlocs` -/
def vlocs (ll : List Loc) : List Var := ll.map vloc
/-- `XTL.vmreg` -/
def vmreg (mr : Mreg) : Var := .L (.R mr)
/-- `XTL.vmregs` -/
def vmregs (mrl : List Mreg) : List Var := mrl.map vmreg

/-- `XTL.vlocpairs` -/
def vlocpairs : List (RPair Loc) → List Var
  | [] => []
  | .One l :: ll => .L l :: vlocpairs ll
  | .Twolong l1 l2 :: ll => .L l1 :: .L l2 :: vlocpairs ll

/-- `XTL.is_stack_reg` -/
def isStackReg : Var → Bool
  | .L (.R r) => Mreg.isStackReg r
  | _ => false

/-! ## Sets of variables -/

/-- `XTL.VSet` -/
abbrev VSet := Std.HashSet Var

/-- Equality of sets of variables (`VSet.equal`). -/
def VSet.equal (s1 s2 : VSet) : Bool := s1.size == s2.size && s1.all (s2.contains ·)

/-- `VSet.union` -/
def VSet.union (s1 s2 : VSet) : VSet := s2.fold (fun s v => s.insert v) s1

/-! ## Generation of fresh registers and fresh register variables -/

/-- The state of the generator of fresh registers (`next_temp`,
    `twin_table`). -/
structure TempState where
  nextTemp : Positive := .xH
  twins : Std.HashMap Positive Positive := {}
  deriving Inhabited

/-- Computations that create fresh registers. -/
abbrev TempM := StateM TempState

/-- `XTL.reset_temps` -/
def resetTemps : TempM Unit := set ({} : TempState)

/-- `XTL.new_reg` -/
def newReg : TempM Reg := do
  let st ← get
  set { st with nextTemp := st.nextTemp.succ }
  return st.nextTemp

/-- `XTL.new_temp` -/
def newTemp (ty : ATyp) : TempM Var := return .V (← newReg) ty

/-- `XTL.twin_reg` -/
def twinReg (r : Reg) : TempM Reg := do
  match (← get).twins.get? r with
  | some t => return t
  | none =>
    let t ← newReg
    modify fun st => { st with twins := st.twins.insert r t }
    return t

/-! ## Successors (for dataflow analysis) -/

/-- `XTL.successors_block` -/
def successorsBlock : Block → List Node
  | .Xbranch s :: _ => [s]
  | .Xtailcall .. :: _ => []
  | .Xcond _ _ s1 s2 :: _ => [s1, s2]
  | .Xjumptable _ tbl :: _ => tbl
  | .Xreturn _ :: _ => []
  | _ :: blk => successorsBlock blk
  | [] => []

/-! ## Type checking for XTL -/

/-- `XTL.set_var_type` -/
def setVarType (v : Var) (ty : ATyp) : Bool := typeof v == ty

/-- `XTL.set_vars_type` -/
def setVarsType : List Var → List ATyp → Bool
  | [], [] => true
  | v1 :: vl, ty1 :: tyl => setVarType v1 ty1 && setVarsType vl tyl
  | _, _ => false

/-- `XTL.type_builtin_arg` -/
def typeBuiltinArg : BuiltinArg Var → ATyp → Bool
  | .BA v, ty => setVarType v ty
  | .BA_splitlong a1 a2, _ => typeBuiltinArg a1 .Tint && typeBuiltinArg a2 .Tint
  | .BA_addptr a1 a2, _ => typeBuiltinArg a1 Tptr && typeBuiltinArg a2 Tptr
  | _, _ => true

/-- `XTL.type_builtin_args` -/
def typeBuiltinArgs : List (BuiltinArg Var) → List ATyp → Bool
  | [], [] => true
  | a :: al, ty :: tyl => typeBuiltinArg a ty && typeBuiltinArgs al tyl
  | _, _ => false

/-- `XTL.type_builtin_res` -/
def typeBuiltinRes : BuiltinRes Var → ATyp → Bool
  | .BR v, ty => setVarType v ty
  | .BR_splitlong a1 a2, _ => typeBuiltinRes a1 .Tint && typeBuiltinRes a2 .Tint
  | _, _ => true

/-- `XTL.type_instr` (`true` if well typed; OCaml raises `Type_error`). -/
def typeInstr : Instruction → Bool
  | .Xmove src dst | .Xspill src dst | .Xreload src dst => typeof src == typeof dst
  | .Xparmove srcs dsts itmp ftmp =>
    srcs.length == dsts.length && (srcs.zip dsts).all (fun (s, d) => typeof s == typeof d) &&
    setVarType itmp .Tint && setVarType ftmp .Tfloat
  | .Xop op args res =>
    let (targs, tres) := typeOfOperation op
    setVarsType args targs && setVarType res tres
  | .Xload chunk addr args dst =>
    setVarsType args (typeOfAddressing addr) && setVarType dst chunk.typ
  | .Xstore chunk addr args src =>
    setVarsType args (typeOfAddressing addr) && setVarType src chunk.typ
  | .Xcall _ (.inl v) _ _ => setVarType v .Tint
  | .Xcall _ (.inr _) _ _ => true
  | .Xtailcall _ (.inl v) _ => setVarType v .Tint
  | .Xtailcall _ (.inr _) _ => true
  | .Xbuiltin ef args res =>
    let sg := ef.sig
    typeBuiltinArgs args (sg.sig_args.map XType.proj) && typeBuiltinRes res sg.sig_res.proj
  | .Xbranch _ => true
  | .Xcond cond args _ _ => setVarsType args (typeOfCondition cond)
  | .Xjumptable arg _ => setVarType arg .Tint
  | .Xreturn _ => true

/-- `XTL.type_block` -/
def typeBlock (blk : Block) : Bool := blk.all typeInstr

/-- `XTL.type_function`: the first ill-typed block, if any (OCaml raises
    `Type_error_at pc`). -/
def typeFunction (f : XFunction) : Option Node :=
  (PTree.elements f.fn_code).findSome? fun (pc, blk) => if typeBlock blk then none else some pc

/-! ## A generic framework for transforming extended basic blocks -/

/-- `XTL.basic_blocks_map`: the number of predecessors of every node (the
    entry point counts as having two). -/
def basicBlocksMap (f : XFunction) : PMap Nat :=
  let addSuccessor (map : PMap Nat) (s : Node) := map.set s (1 + map.get s)
  (PTree.elements f.fn_code).foldl
    (fun map (_, blk) => (successorsBlock blk).foldl addSuccessor map)
    ((PMap.init 0).set f.fn_entrypoint 2)

/-- `XTL.transform_basic_blocks`: transform every extended basic block,
    propagating the state `transf` returns from a block to its successors
    that have only one predecessor. -/
partial def transformBasicBlocks {σ : Type} [Inhabited σ]
    (transf : Node → Block → σ → TempM (Block × σ)) (top : σ) (f : XFunction) :
    TempM XFunction := do
  let bbmap := basicBlocksMap f
  let rec transformBlock (st : σ) (newcode : Code) (pc : Node) (bb : Block) : TempM Code := do
    let (bb', st') ← transf pc bb st
    let newcode' := newcode.set pc bb'
    (successorsBlock bb).foldlM (fun nc s => do
      if bbmap.get s != 1 then return nc
      match f.fn_code.get s with
      | none => return nc
      | some bb => transformBlock st' nc s bb) newcode'
  let newcode ← (PTree.elements f.fn_code).foldlM
    (fun newcode (pc, bb) =>
      if bbmap.get pc ≥ 2 then transformBlock top newcode pc bb else pure newcode)
    PTree.empty
  return { f with fn_code := newcode }

/-! ## A backward dataflow solver

The untrusted analyses of the register allocator (liveness in
`Regalloc.lean`, live ranges in `Splitting.lean`) use Kildall's
`Backward_Dataflow_Solver` in OCaml.  Since their results are not trusted,
they use this simpler worklist solver instead.  The lattice operations run in
a monad, because the live-range lattice of `Splitting` unifies live ranges
when it computes a least upper bound.  The result maps every node to the
value *after* it (the least upper bound of the values `transf` computes for
its successors). -/

/-- The predecessors of every node of a control-flow graph. -/
def predecessors {A : Type} (code : PTree A) (succs : A → List Positive) :
    Std.HashMap Positive (List Positive) :=
  (PTree.elements code).foldl
    (fun m (pc, i) => (succs i).foldl
      (fun m s => m.insert s (pc :: (m.getD s []))) m) {}

/-- A backward fixpoint solver (see above). -/
partial def backwardFixpoint {M : Type → Type} [Monad M] {A L : Type} [Inhabited L]
    (code : PTree A) (succs : A → List Positive) (bot : L)
    (beq : L → L → M Bool) (lub : L → L → M L) (transf : Positive → L → M L) :
    M (Std.HashMap Positive L) := do
  let preds := predecessors code succs
  let rec loop (work : List Positive) (inWork : Std.HashSet Positive)
      (res : Std.HashMap Positive L) : M (Std.HashMap Positive L) := do
    match work with
    | [] => return res
    | n :: rest =>
      let inWork := inWork.erase n
      let before ← transf n (res.getD n bot)
      let mut res := res
      let mut rest := rest
      let mut inWork := inWork
      for p in preds.getD n [] do
        let old := res.getD p bot
        let new ← lub old before
        if !(← beq old new) then
          res := res.insert p new
          if !inWork.contains p then
            rest := p :: rest
            inWork := inWork.insert p
      loop rest inWork res
  let nodes := (PTree.elements code).map (·.1)
  loop nodes (nodes.foldl (fun s n => s.insert n) {}) {}

end XTL
end X86
end CC
