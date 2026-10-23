/-
  [x86-64 instance of `CCLib/backend/Allocation.lean`: the same development, in
  namespace `CC.X86`, over the x86-64 operators, registers and conventions.]

  Register allocation by external oracle and a posteriori validation —
  port of `backend/Allocation.v` (the Rideau–Leroy validator).

  Ported: `move`, `block_shape`, `classify_operation`, `extract_moves`,
  `extract_moves_ext`, `check_succ`, `pair_Iop_block`, `pair_instr_block`,
  `pair_codes`, `pair_entrypoints`, equations and the operations on sets of
  equations (`add_equation` … `ros_compatible_tailcall`), `track_moves`,
  `transfer_use_def`, `transfer_aux`, `transfer`, the semilattice `LEq`,
  `successors_block_shape`, `analyze`, `compat_entry`,
  `check_entrypoints_aux`, `check_entrypoints`, `check_function`,
  `transf_function`, `transf_fundef`, `transf_program`.  Also the parts of
  `Locations.OrderedLoc` the validator needs (`compare`, `diff_low_bound`,
  `diff_high_bound`).

  Differences from Rocq:
  * Sets of equations (`eqs`, two AVL sets kept in sync, ordered by
    register and by location) are one duplicate-free list of equations.
    The range queries `EqSet.elements_between (select_reg_l r)
    (select_reg_h r)` and `EqSet2.elements_between (select_loc_l l)
    (select_loc_h l)` become filters with the same selection predicates, so
    they select the same equations: those on register `r`, and those whose
    location lies between `OrderedLoc.diff_low_bound l` and
    `OrderedLoc.diff_high_bound l` in the `OrderedLoc` order.  The folds in
    `subst_*` traverse these equations in list order instead of AVL order;
    their result does not depend on the order.
  * `classify_operation` returns a non-dependent `OperationKind`.
  * The external allocator `regalloc` (OCaml `Regalloc.ml`, a `Parameter`
    in Rocq) is an explicit argument of `transfFunction`, and `Archi.abi`
    (used by `loc_arguments`) is an explicit argument `win64`.
  * Error messages are strings.
  * The proofs (`Allocproof.v`) are not ported.
-/
import CCLib.x86.RTLtyping
import CCLib.x86.LTL
import CCLib.backend.Kildall

namespace CC
namespace X86

/- `Archi.win64` (a Rocq `Parameter`): whether the Windows x86-64 ABI is used. -/
variable (win64 : Bool)

/-! ## The order `Locations.OrderedLoc` -/

namespace OrderedLoc

/-- `IndexedSlot.index` -/
def slotIndex : Slot → Nat
  | .Local => 1
  | .Incoming => 2
  | .Outgoing => 3

/-- `IndexedTyp.index` -/
def typIndex : ATyp → Nat
  | .Tany32 => 1
  | .Tint => 2
  | .Tsingle => 3
  | .Tany64 => 4
  | .Tfloat => 5
  | .Tlong => 6

/-- `OrderedLoc.compare` (as an `Ordering`). -/
def compare : Loc → Loc → Ordering
  | .R r1, .R r2 => Ord.compare (Mreg.index r1).toNat (Mreg.index r2).toNat
  | .R _, .S .. => .lt
  | .S .., .R _ => .gt
  | .S sl1 ofs1 ty1, .S sl2 ofs2 ty2 =>
      (Ord.compare (slotIndex sl1) (slotIndex sl2)).then
        ((Ord.compare ofs1 ofs2).then (Ord.compare (typIndex ty1) (typIndex ty2)))

/-- `OrderedLoc.diff_low_bound` -/
def diffLowBound (l : Loc) : Loc :=
  match l with
  | .R _ => l
  | .S sl ofs _ => .S sl (ofs - 1) .Tany64

/-- `OrderedLoc.diff_high_bound` -/
def diffHighBound (l : Loc) : Loc :=
  match l with
  | .R _ => l
  | .S sl ofs ty => .S sl (ofs + typesize ty - 1) .Tlong

end OrderedLoc

namespace Allocation

open Op RTLtyping Conventions1 Conventions

/-! ## Structural checks -/

/-- `Allocation.move` -/
inductive Move where
  | MV (src dst : Loc)
  | MVmakelong (src1 src2 dst : Mreg)
  | MVlowlong (src dst : Mreg)
  | MVhighlong (src dst : Mreg)

/-- `Allocation.moves` -/
abbrev Moves := List Move

/-- `Allocation.block_shape` -/
inductive BlockShape where
  | BSnop (mv : Moves) (s : RTL.Node)
  | BSmove (src : Reg) (dst : Reg) (mv : Moves) (s : RTL.Node)
  | BSmakelong (src1 src2 : Reg) (dst : Reg) (mv : Moves) (s : RTL.Node)
  | BSlowlong (src : Reg) (dst : Reg) (mv : Moves) (s : RTL.Node)
  | BShighlong (src : Reg) (dst : Reg) (mv : Moves) (s : RTL.Node)
  | BSop (op : Operation) (args : List Reg) (res : Reg)
      (mv1 : Moves) (args' : List Mreg) (res' : Mreg) (mv2 : Moves) (s : RTL.Node)
  | BSopdead (op : Operation) (args : List Reg) (res : Reg) (mv : Moves) (s : RTL.Node)
  | BSload (chunk : Chunk) (addr : Addressing) (args : List Reg) (dst : Reg)
      (mv1 : Moves) (args' : List Mreg) (dst' : Mreg) (mv2 : Moves) (s : RTL.Node)
  | BSloaddead (chunk : Chunk) (addr : Addressing) (args : List Reg) (dst : Reg)
      (mv : Moves) (s : RTL.Node)
  | BSload2 (addr1 addr2 : Addressing) (args : List Reg) (dst : Reg)
      (mv1 : Moves) (args1' : List Mreg) (dst1' : Mreg)
      (mv2 : Moves) (args2' : List Mreg) (dst2' : Mreg) (mv3 : Moves) (s : RTL.Node)
  | BSload2_1 (addr : Addressing) (args : List Reg) (dst : Reg)
      (mv1 : Moves) (args' : List Mreg) (dst' : Mreg) (mv2 : Moves) (s : RTL.Node)
  | BSload2_2 (addr addr' : Addressing) (args : List Reg) (dst : Reg)
      (mv1 : Moves) (args' : List Mreg) (dst' : Mreg) (mv2 : Moves) (s : RTL.Node)
  | BSstore (chunk : Chunk) (addr : Addressing) (args : List Reg) (src : Reg)
      (mv1 : Moves) (args' : List Mreg) (src' : Mreg) (s : RTL.Node)
  | BSstore2 (addr1 addr2 : Addressing) (args : List Reg) (src : Reg)
      (mv1 : Moves) (args1' : List Mreg) (src1' : Mreg)
      (mv2 : Moves) (args2' : List Mreg) (src2' : Mreg) (s : RTL.Node)
  | BScall (sg : Signature) (ros : Sum Reg Ident) (args : List Reg) (res : Reg)
      (mv1 : Moves) (ros' : Sum Mreg Ident) (mv2 : Moves) (s : RTL.Node)
  | BStailcall (sg : Signature) (ros : Sum Reg Ident) (args : List Reg)
      (mv1 : Moves) (ros' : Sum Mreg Ident)
  | BSbuiltin (ef : ExtFun) (args : List (BuiltinArg Reg)) (res : BuiltinRes Reg)
      (mv1 : Moves) (args' : List (BuiltinArg Loc)) (res' : BuiltinRes Mreg)
      (mv2 : Moves) (s : RTL.Node)
  | BScond (cond : Condition) (args : List Reg) (mv : Moves) (args' : List Mreg)
      (s1 s2 : RTL.Node)
  | BSjumptable (arg : Reg) (mv : Moves) (arg' : Mreg) (tbl : List RTL.Node)
  | BSreturn (arg : Option Reg) (mv : Moves)

/-- `Allocation.operation_kind` (non-dependent version). -/
inductive OperationKind (A : Type) where
  | Omove (arg : A)
  | Omakelong (arg1 arg2 : A)
  | Olowlong (arg : A)
  | Ohighlong (arg : A)
  | other

/-- `Allocation.classify_operation` -/
def classifyOperation {A : Type} (op : Operation) (args : List A) : OperationKind A :=
  match op, args with
  | .Omove, [arg] => .Omove arg
  | .Omakelong, [arg1, arg2] => .Omakelong arg1 arg2
  | .Olowlong, [arg] => .Olowlong arg
  | .Ohighlong, [arg] => .Ohighlong arg
  | _, _ => .other

/-- `Allocation.extract_moves` -/
def extractMoves (accu : Moves) : LTL.Bblock → Moves × LTL.Bblock
  | .Lgetstack sl ofs ty dst :: b' => extractMoves (.MV (.S sl ofs ty) (.R dst) :: accu) b'
  | .Lsetstack src sl ofs ty :: b' => extractMoves (.MV (.R src) (.S sl ofs ty) :: accu) b'
  | .Lop op args res :: b' =>
      match isMoveOperation op args with
      | some arg => extractMoves (.MV (.R arg) (.R res) :: accu) b'
      | none => (accu.reverse, .Lop op args res :: b')
  | b => (accu.reverse, b)

/-- `Allocation.extract_moves_ext` -/
def extractMovesExt (accu : Moves) : LTL.Bblock → Moves × LTL.Bblock
  | .Lgetstack sl ofs ty dst :: b' => extractMovesExt (.MV (.S sl ofs ty) (.R dst) :: accu) b'
  | .Lsetstack src sl ofs ty :: b' => extractMovesExt (.MV (.R src) (.S sl ofs ty) :: accu) b'
  | .Lop op args res :: b' =>
      match classifyOperation op args with
      | .Omove arg => extractMovesExt (.MV (.R arg) (.R res) :: accu) b'
      | .Omakelong arg1 arg2 => extractMovesExt (.MVmakelong arg1 arg2 res :: accu) b'
      | .Olowlong arg => extractMovesExt (.MVlowlong arg res :: accu) b'
      | .Ohighlong arg => extractMovesExt (.MVhighlong arg res :: accu) b'
      | .other => (accu.reverse, .Lop op args res :: b')
  | b => (accu.reverse, b)

/-- `Allocation.check_succ` -/
def checkSucc (s : RTL.Node) (b : LTL.Bblock) : Bool :=
  match b with
  | .Lbranch s' :: _ => decide (s = s')
  | _ => false

/-- `Allocation.pair_Iop_block` -/
def pairIopBlock (op : Operation) (args : List Reg) (res : Reg) (s : RTL.Node)
    (b : LTL.Bblock) : Option BlockShape :=
  let (mv1, b1) := extractMoves [] b
  match b1 with
  | .Lop op' args' res' :: b2 =>
      let (mv2, b3) := extractMoves [] b2
      if decide (op = op') && checkSucc s b3 then
        some (.BSop op args res mv1 args' res' mv2 s)
      else none
  | _ =>
      if checkSucc s b1 then some (.BSopdead op args res mv1 s) else none

/-- Helper for the `Archi.splitlong` cases of `pair_instr_block`. -/
def pairSplit (s : RTL.Node) (b : LTL.Bblock) (k : Moves → BlockShape) :
    Option BlockShape :=
  let (mv, b1) := extractMoves [] b
  if checkSucc s b1 then some (k mv) else none

/-- `Allocation.pair_instr_block` -/
def pairInstrBlock (i : RTL.Instruction) (b : LTL.Bblock) : Option BlockShape :=
  match i with
  | .Inop s => pairSplit s b (fun mv => .BSnop mv s)
  | .Iop op args res s =>
      match classifyOperation op args with
      | .Omove arg => pairSplit s b (fun mv => .BSmove arg res mv s)
      | .Omakelong arg1 arg2 =>
          if Archi.splitlong then pairSplit s b (fun mv => .BSmakelong arg1 arg2 res mv s)
          else pairIopBlock op args res s b
      | .Olowlong arg =>
          if Archi.splitlong then pairSplit s b (fun mv => .BSlowlong arg res mv s)
          else pairIopBlock op args res s b
      | .Ohighlong arg =>
          if Archi.splitlong then pairSplit s b (fun mv => .BShighlong arg res mv s)
          else pairIopBlock op args res s b
      | .other => pairIopBlock op args res s b
  | .Iload chunk addr args dst s =>
      let (mv1, b1) := extractMoves [] b
      match b1 with
      | .Lload chunk' addr' args' dst' :: b2 =>
          if decide (chunk = .Mint64) && Archi.splitlong then
            if decide (chunk' = .Mint32) then
              let (mv2, b3) := extractMoves [] b2
              match b3 with
              | .Lload chunk'' addr'' args'' dst'' :: b4 =>
                  let (mv3, b5) := extractMoves [] b4
                  if decide (chunk'' = .Mint32) && decide (addr = addr') &&
                      decide (offsetAddressing addr 4 = some addr'') && checkSucc s b5 then
                    some (.BSload2 addr addr'' args dst mv1 args' dst' mv2 args'' dst'' mv3 s)
                  else none
              | _ =>
                  if checkSucc s b3 then
                    if decide (addr = addr') then
                      some (.BSload2_1 addr args dst mv1 args' dst' mv2 s)
                    else if decide (offsetAddressing addr 4 = some addr') then
                      some (.BSload2_2 addr addr' args dst mv1 args' dst' mv2 s)
                    else none
                  else none
            else none
          else
            let (mv2, b3) := extractMoves [] b2
            if decide (chunk = chunk') && decide (addr = addr') && checkSucc s b3 then
              some (.BSload chunk addr args dst mv1 args' dst' mv2 s)
            else none
      | _ =>
          if checkSucc s b1 then some (.BSloaddead chunk addr args dst mv1 s) else none
  | .Istore chunk addr args src s =>
      let (mv1, b1) := extractMoves [] b
      match b1 with
      | .Lstore chunk' addr' args' src' :: b2 =>
          if decide (chunk = .Mint64) && Archi.splitlong then
            let (mv2, b3) := extractMoves [] b2
            match b3 with
            | .Lstore chunk'' addr'' args'' src'' :: b4 =>
                if decide (chunk' = .Mint32) && decide (chunk'' = .Mint32) &&
                    decide (addr = addr') && decide (offsetAddressing addr 4 = some addr'') &&
                    checkSucc s b4 then
                  some (.BSstore2 addr addr'' args src mv1 args' src' mv2 args'' src'' s)
                else none
            | _ => none
          else
            if decide (chunk = chunk') && decide (addr = addr') && checkSucc s b2 then
              some (.BSstore chunk addr args src mv1 args' src' s)
            else none
      | _ => none
  | .Icall sg ros args res s =>
      let (mv1, b1) := extractMovesExt [] b
      match b1 with
      | .Lcall sg' ros' :: b2 =>
          let (mv2, b3) := extractMovesExt [] b2
          if decide (sg = sg') && checkSucc s b3 then
            some (.BScall sg ros args res mv1 ros' mv2 s)
          else none
      | _ => none
  | .Itailcall sg ros args =>
      let (mv1, b1) := extractMovesExt [] b
      match b1 with
      | .Ltailcall sg' ros' :: _ =>
          if decide (sg = sg') then some (.BStailcall sg ros args mv1 ros') else none
      | _ => none
  | .Ibuiltin ef args res s =>
      let (mv1, b1) := extractMoves [] b
      match b1 with
      | .Lbuiltin ef' args' res' :: b2 =>
          let (mv2, b3) := extractMoves [] b2
          if decide (ef = ef') && checkSucc s b3 then
            some (.BSbuiltin ef args res mv1 args' res' mv2 s)
          else none
      | _ => none
  | .Icond cond args s1 s2 =>
      let (mv1, b1) := extractMoves [] b
      match b1 with
      | .Lcond cond' args' s1' s2' :: _ =>
          if decide (cond = cond') && decide (s1 = s1') && decide (s2 = s2') then
            some (.BScond cond args mv1 args' s1 s2)
          else none
      | _ => none
  | .Ijumptable arg tbl =>
      let (mv1, b1) := extractMoves [] b
      match b1 with
      | .Ljumptable arg' tbl' :: _ =>
          if decide (tbl = tbl') then some (.BSjumptable arg mv1 arg' tbl) else none
      | _ => none
  | .Ireturn arg =>
      let (mv1, b1) := extractMovesExt [] b
      match b1 with
      | .Lreturn :: _ => some (.BSreturn arg mv1)
      | _ => none

/-- `Allocation.pair_codes` -/
def pairCodes (f1 : RTL.Function) (f2 : LTL.Function) : PTree BlockShape :=
  PTree.combine
    (fun opti optb => match opti, optb with
      | some i, some b => pairInstrBlock i b
      | _, _ => none)
    f1.fn_code f2.fn_code

/-- `Allocation.pair_entrypoints` -/
def pairEntrypoints (f1 : RTL.Function) (f2 : LTL.Function) : Option Moves :=
  match f2.fn_code.get f2.fn_entrypoint with
  | none => none
  | some b =>
      let (mv, b1) := extractMovesExt [] b
      if checkSucc f1.fn_entrypoint b1 then some mv else none

/-! ## Sets of equations between RTL registers and LTL locations -/

/-- `Allocation.equation_kind` -/
inductive EquationKind where
  | Full | Low | High
  deriving DecidableEq, Repr

/-- `Allocation.equation` -/
structure Equation where
  ekind : EquationKind
  ereg : Reg
  eloc : Loc
  deriving DecidableEq

/-- `Allocation.eqs`: a duplicate-free list of equations. -/
abbrev Eqs := List Equation

namespace Eqs

/-- `empty_eqs` -/
def empty : Eqs := []
/-- `EqSet.mem` -/
def mem (q : Equation) (e : Eqs) : Bool := e.contains q
/-- `add_equation` -/
def add (q : Equation) (e : Eqs) : Eqs := if mem q e then e else q :: e
/-- `remove_equation` -/
def remove (q : Equation) (e : Eqs) : Eqs := e.filter (fun x => x != q)
/-- `EqSet.union` -/
def union (s1 s2 : Eqs) : Eqs := s1.foldr add s2
/-- `EqSet.subset` -/
def subset (s1 s2 : Eqs) : Bool := s1.all (fun q => mem q s2)
/-- `EqSet.equal` -/
def equal (s1 s2 : Eqs) : Bool := subset s1 s2 && subset s2 s1
/-- `EqSet.Subset` -/
def Subset (s1 s2 : Eqs) : Prop := ∀ q, q ∈ s1 → q ∈ s2
/-- `EqSet.Equal` -/
def Equal (s1 s2 : Eqs) : Prop := ∀ q, q ∈ s1 ↔ q ∈ s2

theorem mem_iff {q : Equation} {s : Eqs} : mem q s = true ↔ q ∈ s := by
  simp [mem]

theorem mem_add {q x : Equation} {s : Eqs} : q ∈ add x s ↔ q = x ∨ q ∈ s := by
  unfold add
  split
  · next h =>
    rw [mem_iff] at h
    constructor
    · exact .inr
    · rintro (rfl | h')
      · exact h
      · exact h'
  · simp

theorem mem_remove {q x : Equation} {s : Eqs} : q ∈ remove x s ↔ q ≠ x ∧ q ∈ s := by
  simp [remove, and_comm]

theorem mem_union {q : Equation} {s1 s2 : Eqs} : q ∈ union s1 s2 ↔ q ∈ s1 ∨ q ∈ s2 := by
  induction s1 with
  | nil => simp [union]
  | cons x l ih =>
    show q ∈ add x (union l s2) ↔ _
    rw [mem_add, ih]
    simp only [List.mem_cons]
    constructor
    · rintro (h | h | h)
      · exact .inl (.inl h)
      · exact .inl (.inr h)
      · exact .inr h
    · rintro ((h | h) | h)
      · exact .inl h
      · exact .inr (.inl h)
      · exact .inr (.inr h)

theorem subset_iff {s1 s2 : Eqs} : subset s1 s2 = true ↔ Subset s1 s2 := by
  simp [subset, Subset, mem]

end Eqs

open Eqs (add remove)

/-- `Allocation.select_reg_l` and `select_reg_h` combined: the equations on `r`. -/
def selectReg (r : Reg) (q : Equation) : Bool := decide (q.ereg = r)

/-- `EqSet.elements_between (select_reg_l r) (select_reg_h r)` -/
def eqsOfReg (r : Reg) (e : Eqs) : Eqs := e.filter (selectReg r)

/-- `Allocation.reg_unconstrained` -/
def regUnconstrained (r : Reg) (e : Eqs) : Bool := !(e.any (selectReg r))

/-- `Allocation.select_loc_l` -/
def selectLocL (l : Loc) (q : Equation) : Bool :=
  OrderedLoc.compare q.eloc (OrderedLoc.diffLowBound l) != .lt

/-- `Allocation.select_loc_h` -/
def selectLocH (l : Loc) (q : Equation) : Bool :=
  OrderedLoc.compare q.eloc (OrderedLoc.diffHighBound l) != .gt

/-- Both bounds of the location range. -/
def selectLoc (l : Loc) (q : Equation) : Bool := selectLocL l q && selectLocH l q

/-- `EqSet2.elements_between (select_loc_l l) (select_loc_h l)` -/
def eqsOfLoc (l : Loc) (e : Eqs) : Eqs := e.filter (selectLoc l)

/-- `Allocation.loc_unconstrained` -/
def locUnconstrained (l : Loc) (e : Eqs) : Bool := !(e.any (selectLoc l))

/-- `Allocation.reg_loc_unconstrained` -/
def regLocUnconstrained (r : Reg) (l : Loc) (e : Eqs) : Bool :=
  regUnconstrained r e && locUnconstrained l e

/-- `Allocation.subst_reg` -/
def substReg (r1 r2 : Reg) (e : Eqs) : Eqs :=
  (eqsOfReg r1 e).foldl (fun e q => add ⟨q.ekind, r2, q.eloc⟩ (remove q e)) e

/-- `Allocation.subst_reg_kind` -/
def substRegKind (r1 : Reg) (k1 : EquationKind) (r2 : Reg) (k2 : EquationKind) (e : Eqs) : Eqs :=
  (eqsOfReg r1 e).foldl
    (fun e q => if q.ekind = k1 then add ⟨k2, r2, q.eloc⟩ (remove q e) else e) e

/-- `Allocation.subst_loc` -/
def substLoc (l1 l2 : Loc) (e : Eqs) : Option Eqs :=
  (eqsOfLoc l1 e).foldl
    (fun opte q => match opte with
      | none => none
      | some e => if l1 = q.eloc then some (add ⟨q.ekind, q.ereg, l2⟩ (remove q e)) else none)
    (some e)

/-- `Allocation.subst_loc_part` -/
def substLocPart (l1 l2 : Loc) (k : EquationKind) (e : Eqs) : Option Eqs :=
  (eqsOfLoc l1 e).foldl
    (fun opte q => match opte with
      | none => none
      | some e =>
          if l1 = q.eloc then
            if q.ekind = k then some (add ⟨.Full, q.ereg, l2⟩ (remove q e)) else none
          else none)
    (some e)

/-- `Allocation.subst_loc_pair` -/
def substLocPair (l1 l2 l2' : Loc) (e : Eqs) : Option Eqs :=
  (eqsOfLoc l1 e).foldl
    (fun opte q => match opte with
      | none => none
      | some e =>
          if l1 = q.eloc then
            if q.ekind = .Full then
              some (add ⟨.High, q.ereg, l2⟩ (add ⟨.Low, q.ereg, l2'⟩ (remove q e)))
            else none
          else none)
    (some e)

/-- `Allocation.sel_type` -/
def selType (k : EquationKind) (ty : ATyp) : ATyp :=
  match k with
  | .Full => ty
  | .Low | .High => .Tint

/-- `Allocation.loc_type_compat` -/
def locTypeCompat (env : Regenv) (l : Loc) (e : Eqs) : Bool :=
  (eqsOfLoc l e).all (fun q => ATyp.subtype (selType q.ekind (env q.ereg)) l.type)

/-- `Allocation.long_type_compat` -/
def longTypeCompat (env : Regenv) (l : Loc) (e : Eqs) : Bool :=
  (eqsOfLoc l e).all (fun q => ATyp.subtype (env q.ereg) .Tlong)

/-- `Allocation.add_equations` -/
def addEquations : List Reg → List Mreg → Eqs → Option Eqs
  | [], [], e => some e
  | r1 :: rl, m1 :: ml, e => addEquations rl ml (add ⟨.Full, r1, .R m1⟩ e)
  | _, _, _ => none

/-- `Allocation.add_equations_args` -/
def addEquationsArgs : List Reg → List ATyp → List (RPair Loc) → Eqs → Option Eqs
  | [], [], [], e => some e
  | r1 :: rl, _ :: tyl, .One l1 :: ll, e => addEquationsArgs rl tyl ll (add ⟨.Full, r1, l1⟩ e)
  | r1 :: rl, .Tlong :: tyl, .Twolong l1 l2 :: ll, e =>
      if Archi.ptr64 then none
      else addEquationsArgs rl tyl ll (add ⟨.Low, r1, l2⟩ (add ⟨.High, r1, l1⟩ e))
  | _, _, _, _ => none

/-- `Allocation.add_equations_res` -/
def addEquationsRes (r : Reg) (ty : ATyp) (p : RPair Mreg) (e : Eqs) : Option Eqs :=
  match p, ty with
  | .One mr, _ => some (add ⟨.Full, r, .R mr⟩ e)
  | .Twolong mr1 mr2, .Tlong =>
      if Archi.ptr64 then none
      else some (add ⟨.Low, r, .R mr2⟩ (add ⟨.High, r, .R mr1⟩ e))
  | _, _ => none

/-- `Allocation.remove_equations_res` -/
def removeEquationsRes (r : Reg) (p : RPair Mreg) (e : Eqs) : Option Eqs :=
  match p with
  | .One mr => some (remove ⟨.Full, r, .R mr⟩ e)
  | .Twolong mr1 mr2 =>
      if mr2 = mr1 then none
      else some (remove ⟨.Low, r, .R mr2⟩ (remove ⟨.High, r, .R mr1⟩ e))

/-- `Allocation.add_equation_ros` -/
def addEquationRos (ros : Sum Reg Ident) (ros' : Sum Mreg Ident) (e : Eqs) : Option Eqs :=
  match ros, ros' with
  | .inl r, .inl mr => some (add ⟨.Full, r, .R mr⟩ e)
  | .inr id, .inr id' => if id = id' then some e else none
  | _, _ => none

/-- `Allocation.add_equations_builtin_arg` -/
def addEquationsBuiltinArg (env : Regenv) :
    BuiltinArg Reg → BuiltinArg Loc → Eqs → Option Eqs
  | .BA r, .BA l, e => some (add ⟨.Full, r, l⟩ e)
  | .BA r, .BA_splitlong (.BA lhi) (.BA llo), e =>
      if env r = .Tlong && Archi.splitlong then
        some (add ⟨.Low, r, llo⟩ (add ⟨.High, r, lhi⟩ e))
      else none
  | .BA_int n, .BA_int n', e => if n = n' then some e else none
  | .BA_long n, .BA_long n', e => if n = n' then some e else none
  | .BA_float f, .BA_float f', e => if f = f' then some e else none
  | .BA_single f, .BA_single f', e => if f = f' then some e else none
  | .BA_loadstack chunk ofs, .BA_loadstack chunk' ofs', e =>
      if chunk = chunk' && ofs = ofs' then some e else none
  | .BA_addrstack ofs, .BA_addrstack ofs', e => if ofs = ofs' then some e else none
  | .BA_loadglobal chunk id ofs, .BA_loadglobal chunk' id' ofs', e =>
      if chunk = chunk' && id = id' && ofs = ofs' then some e else none
  | .BA_addrglobal id ofs, .BA_addrglobal id' ofs', e =>
      if id = id' && ofs = ofs' then some e else none
  | .BA_splitlong hi lo, .BA_splitlong hi' lo', e =>
      match addEquationsBuiltinArg env hi hi' e with
      | none => none
      | some e1 => addEquationsBuiltinArg env lo lo' e1
  | .BA_addptr a1 a2, .BA_addptr a1' a2', e =>
      match addEquationsBuiltinArg env a1 a1' e with
      | none => none
      | some e1 => addEquationsBuiltinArg env a2 a2' e1
  | _, _, _ => none

/-- `Allocation.add_equations_builtin_args` -/
def addEquationsBuiltinArgs (env : Regenv) :
    List (BuiltinArg Reg) → List (BuiltinArg Loc) → Eqs → Option Eqs
  | [], [], e => some e
  | a1 :: al, a1' :: al', e =>
      match addEquationsBuiltinArg env a1 a1' e with
      | none => none
      | some e1 => addEquationsBuiltinArgs env al al' e1
  | _, _, _ => none

/-- `Allocation.add_equations_debug_args` -/
def addEquationsDebugArgs (env : Regenv) :
    List (BuiltinArg Reg) → List (BuiltinArg Loc) → Eqs → Option Eqs
  | _, [], e => some e
  | a1 :: al, a1' :: al', e =>
      match addEquationsBuiltinArg env a1 a1' e with
      | none => addEquationsDebugArgs env al (a1' :: al') e
      | some e1 => addEquationsDebugArgs env al al' e1
  | _, _, _ => none

/-- `Allocation.remove_equations_builtin_res` -/
def removeEquationsBuiltinRes (env : Regenv) (res : BuiltinRes Reg) (res' : BuiltinRes Mreg)
    (e : Eqs) : Option Eqs :=
  match res, res' with
  | .BR r, .BR r' => some (remove ⟨.Full, r, .R r'⟩ e)
  | .BR r, .BR_splitlong (.BR rhi) (.BR rlo) =>
      if env r = .Tlong then
        if rhi = rlo then none
        else some (remove ⟨.Low, r, .R rlo⟩ (remove ⟨.High, r, .R rhi⟩ e))
      else none
  | .BR_none, .BR_none => some e
  | _, _ => none

/-- `Allocation.can_undef` -/
def canUndef (ml : List Mreg) (e : Eqs) : Bool := ml.all (fun m => locUnconstrained (.R m) e)

/-- `Allocation.can_undef_except` -/
def canUndefExcept (l : Loc) (ml : List Mreg) (e : Eqs) : Bool :=
  ml.all (fun m => decide (l = .R m) || locUnconstrained (.R m) e)

/-- `Allocation.no_caller_saves` -/
def noCallerSaves (e : Eqs) : Bool :=
  e.all (fun q => match q.eloc with
    | .R r => isCalleeSave win64 r
    | .S .Outgoing _ _ => false
    | .S _ _ _ => true)

/-- `Allocation.compat_left` -/
def compatLeft (r : Reg) (l : Loc) (e : Eqs) : Bool :=
  (eqsOfReg r e).all (fun q => match q.ekind with
    | .Full => decide (l = q.eloc)
    | _ => false)

/-- `Allocation.compat_left2` -/
def compatLeft2 (r : Reg) (l1 l2 : Loc) (e : Eqs) : Bool :=
  (eqsOfReg r e).all (fun q => match q.ekind with
    | .High => decide (l1 = q.eloc)
    | .Low => decide (l2 = q.eloc)
    | _ => false)

/-- `Allocation.ros_compatible_tailcall` -/
def rosCompatibleTailcall (ros : Sum Mreg Ident) : Bool :=
  match ros with
  | .inl r => !isCalleeSave win64 r
  | .inr _ => true

/-! ## The validator -/

/-- `Allocation.destroyed_by_move` -/
def destroyedByMove (src dst : Loc) : List Mreg :=
  match src, dst with
  | .S sl _ _, _ => LTL.destroyedByGetstack sl
  | _, .S _ _ ty => destroyedBySetstack ty
  | _, _ => destroyedByOp .Omove

/-- `Allocation.well_typed_move` -/
def wellTypedMove (env : Regenv) (dst : Loc) (e : Eqs) : Bool :=
  match dst with
  | .R _ => true
  | .S .. => locTypeCompat env dst e

/-- `Allocation.track_moves` -/
def trackMoves (env : Regenv) : Moves → Eqs → Option Eqs
  | [], e => some e
  | .MV src dst :: mv, e =>
      match trackMoves env mv e with
      | none => none
      | some e1 =>
          if canUndefExcept dst (destroyedByMove src dst) e1 && wellTypedMove env dst e1 then
            substLoc dst src e1
          else none
  | .MVmakelong src1 src2 dst :: mv, e =>
      if !Archi.ptr64 then
        match trackMoves env mv e with
        | none => none
        | some e1 =>
            if longTypeCompat env (.R dst) e1 then substLocPair (.R dst) (.R src1) (.R src2) e1
            else none
      else none
  | .MVlowlong src dst :: mv, e =>
      if !Archi.ptr64 then
        match trackMoves env mv e with
        | none => none
        | some e1 => substLocPart (.R dst) (.R src) .Low e1
      else none
  | .MVhighlong src dst :: mv, e =>
      if !Archi.ptr64 then
        match trackMoves env mv e with
        | none => none
        | some e1 => substLocPart (.R dst) (.R src) .High e1
      else none

/-- `Allocation.transfer_use_def` -/
def transferUseDef (args : List Reg) (res : Reg) (args' : List Mreg) (res' : Mreg)
    (undefs : List Mreg) (e : Eqs) : Option Eqs :=
  let e1 := remove ⟨.Full, res, .R res'⟩ e
  if regLocUnconstrained res (.R res') e1 && canUndef undefs e1 then addEquations args args' e1
  else none

/-- `Allocation.kind_first_word` -/
def kindFirstWord : EquationKind := if Archi.big_endian then .High else .Low
/-- `Allocation.kind_second_word` -/
def kindSecondWord : EquationKind := if Archi.big_endian then .Low else .High

section TRANSFER
variable (win64 : Bool)

/-- `Allocation.transfer_aux` -/
def transferAux (f : RTL.Function) (env : Regenv) (shape : BlockShape) (e : Eqs) : Option Eqs :=
  match shape with
  | .BSnop mv _ => trackMoves env mv e
  | .BSmove src dst mv _ => trackMoves env mv (substReg dst src e)
  | .BSmakelong src1 src2 dst mv _ =>
      let e1 := substRegKind dst .High src1 .Full e
      let e2 := substRegKind dst .Low src2 .Full e1
      if regUnconstrained dst e2 then trackMoves env mv e2 else none
  | .BSlowlong src dst mv _ =>
      let e1 := substRegKind dst .Full src .Low e
      if regUnconstrained dst e1 then trackMoves env mv e1 else none
  | .BShighlong src dst mv _ =>
      let e1 := substRegKind dst .Full src .High e
      if regUnconstrained dst e1 then trackMoves env mv e1 else none
  | .BSop op args res mv1 args' res' mv2 _ => do
      let e1 ← trackMoves env mv2 e
      let e2 ← transferUseDef args res args' res' (destroyedByOp op) e1
      trackMoves env mv1 e2
  | .BSopdead _ _ res mv _ =>
      if regUnconstrained res e then trackMoves env mv e else none
  | .BSload chunk addr args dst mv1 args' dst' mv2 _ => do
      let e1 ← trackMoves env mv2 e
      let e2 ← transferUseDef args dst args' dst' (destroyedByLoad chunk addr) e1
      trackMoves env mv1 e2
  | .BSload2 addr addr' args dst mv1 args1' dst1' mv2 args2' dst2' mv3 _ => do
      let e1 ← trackMoves env mv3 e
      let e2 := remove ⟨kindSecondWord, dst, .R dst2'⟩ e1
      if !(locUnconstrained (.R dst2') e2 && canUndef (destroyedByLoad .Mint32 addr') e2) then
        none
      else
      let e3 ← addEquations args args2' e2
      let e4 ← trackMoves env mv2 e3
      let e5 := remove ⟨kindFirstWord, dst, .R dst1'⟩ e4
      if !(locUnconstrained (.R dst1') e5 && canUndef (destroyedByLoad .Mint32 addr) e5 &&
          regUnconstrained dst e5) then
        none
      else
      let e6 ← addEquations args args1' e5
      trackMoves env mv1 e6
  | .BSload2_1 addr args dst mv1 args' dst' mv2 _ => do
      let e1 ← trackMoves env mv2 e
      let e2 := remove ⟨kindFirstWord, dst, .R dst'⟩ e1
      if !(regLocUnconstrained dst (.R dst') e2 &&
          canUndef (destroyedByLoad .Mint32 addr) e2) then
        none
      else
      let e3 ← addEquations args args' e2
      trackMoves env mv1 e3
  | .BSload2_2 _ addr' args dst mv1 args' dst' mv2 _ => do
      let e1 ← trackMoves env mv2 e
      let e2 := remove ⟨kindSecondWord, dst, .R dst'⟩ e1
      if !(regLocUnconstrained dst (.R dst') e2 &&
          canUndef (destroyedByLoad .Mint32 addr') e2) then
        none
      else
      let e3 ← addEquations args args' e2
      trackMoves env mv1 e3
  | .BSloaddead _ _ _ dst mv _ =>
      if regUnconstrained dst e then trackMoves env mv e else none
  | .BSstore chunk addr args src mv args' src' _ =>
      if canUndef (destroyedByStore chunk addr) e then do
        let e1 ← addEquations (src :: args) (src' :: args') e
        trackMoves env mv e1
      else none
  | .BSstore2 addr addr' args src mv1 args1' src1' mv2 args2' src2' _ =>
      if canUndef (destroyedByStore .Mint32 addr') e then do
        let e1 ← addEquations args args2' (add ⟨kindSecondWord, src, .R src2'⟩ e)
        let e2 ← trackMoves env mv2 e1
        if canUndef (destroyedByStore .Mint32 addr) e2 then do
          let e3 ← addEquations args args1' (add ⟨kindFirstWord, src, .R src1'⟩ e2)
          trackMoves env mv1 e3
        else none
      else none
  | .BScall sg ros args res mv1 ros' mv2 _ => do
      let args' := locArguments win64 sg
      let res' := locResult sg
      let e1 ← trackMoves env mv2 e
      let e2 ← removeEquationsRes res res' e1
      if !((RPair.regs res').all (fun r => regLocUnconstrained res (.R r) e2) &&
          noCallerSaves win64 e2) then
        none
      else
      let e3 ← addEquationRos ros ros' e2
      let e4 ← addEquationsArgs args (Conventions1.projSigArgs sg) args' e3
      trackMoves env mv1 e4
  | .BStailcall sg ros args mv1 ros' =>
      let args' := locArguments win64 sg
      if tailcallIsPossible win64 sg && decide (sg.sig_res = f.fn_sig.sig_res) &&
          rosCompatibleTailcall win64 ros' then do
        let e1 ← addEquationRos ros ros' Eqs.empty
        let e2 ← addEquationsArgs args (Conventions1.projSigArgs sg) args' e1
        trackMoves env mv1 e2
      else none
  | .BSbuiltin ef args res mv1 args' res' mv2 _ => do
      let e1 ← trackMoves env mv2 e
      let e2 ← removeEquationsBuiltinRes env res res' e1
      if !((BuiltinRes.params res).all (fun r => regUnconstrained r e2) &&
          (BuiltinRes.params res').all (fun mr => locUnconstrained (.R mr) e2) &&
          canUndef (destroyedByBuiltin ef) e2) then
        none
      else
      let e3 ← match ef with
        | .EF_debug _ _ _ => addEquationsDebugArgs env args args' e2
        | _ => addEquationsBuiltinArgs env args args' e2
      trackMoves env mv1 e3
  | .BScond cond args mv args' _ _ =>
      if canUndef (destroyedByCond cond) e then do
        let e1 ← addEquations args args' e
        trackMoves env mv e1
      else none
  | .BSjumptable arg mv arg' _ =>
      if canUndef destroyedByJumptable e then
        trackMoves env mv (add ⟨.Full, arg, .R arg'⟩ e)
      else none
  | .BSreturn none mv => trackMoves env mv Eqs.empty
  | .BSreturn (some arg) mv => do
      let arg' := locResult f.fn_sig
      let e1 ← addEquationsRes arg (Conventions1.projSigRes f.fn_sig) arg' Eqs.empty
      trackMoves env mv e1

/-- `Allocation.transfer` -/
def transfer (f : RTL.Function) (env : Regenv) (shapes : PTree BlockShape) (pc : RTL.Node)
    (after : Res Eqs) : Res Eqs :=
  match after with
  | .Error _ => after
  | .OK e =>
      match shapes.get pc with
      | none => .Error s!"At PC {pc.toNat}: unmatched block"
      | some shape =>
          match transferAux win64 f env shape e with
          | none => .Error s!"At PC {pc.toNat}: invalid register allocation"
          | some e' => .OK e'

end TRANSFER

/-- `Allocation.LEq`: analysis results `res eqs`, errors being `Top` and sets
    of equations being ordered by inclusion. -/
instance LEq : Semilattice (Res Eqs) where
  eq x y := match x, y with
    | .OK a, .OK b => Eqs.Equal a b
    | .Error _, .Error _ => True
    | _, _ => False
  eq_refl x := by cases x <;> simp [Eqs.Equal]
  eq_sym {x y} h := by
    cases x <;> cases y <;> simp_all [Eqs.Equal]
  eq_trans {x y z} h1 h2 := by
    cases x <;> cases y <;> cases z <;> simp_all [Eqs.Equal]
  beq x y := match x, y with
    | .OK a, .OK b => Eqs.equal a b
    | .Error _, .Error _ => true
    | _, _ => false
  beq_correct {x y} h := by
    cases x <;> cases y <;> simp_all
    rename_i a b
    simp only [Eqs.equal, Bool.and_eq_true, Eqs.subset_iff] at h
    exact fun q => ⟨h.1 q, h.2 q⟩
  ge x y := match x, y with
    | .OK a, .OK b => Eqs.Subset b a
    | .Error _, _ => True
    | _, .Error _ => False
  ge_refl {x y} h := by
    cases x <;> cases y <;> simp_all [Eqs.Equal, Eqs.Subset]
  ge_trans {x y z} h1 h2 := by
    cases x <;> cases y <;> cases z <;> simp_all [Eqs.Subset]
  bot := .OK Eqs.empty
  ge_bot x := by cases x <;> simp [Eqs.Subset, Eqs.empty]
  lub x y := match x, y with
    | .OK a, .OK b => .OK (Eqs.union a b)
    | .OK _, .Error _ => y
    | .Error _, _ => x
  ge_lub_left x y := by
    cases x <;> cases y <;> simp [Eqs.Subset, Eqs.mem_union] <;> exact fun _ h => .inl h
  ge_lub_right x y := by
    cases x <;> cases y <;> simp [Eqs.Subset, Eqs.mem_union] <;> exact fun _ h => .inr h

/-- `Allocation.successors_block_shape` -/
def successorsBlockShape (bsh : BlockShape) : List RTL.Node :=
  match bsh with
  | .BSnop _ s | .BSmove _ _ _ s | .BSmakelong _ _ _ _ s | .BSlowlong _ _ _ s
  | .BShighlong _ _ _ s | .BSop _ _ _ _ _ _ _ s | .BSopdead _ _ _ _ s
  | .BSload _ _ _ _ _ _ _ _ s | .BSload2 _ _ _ _ _ _ _ _ _ _ _ s
  | .BSload2_1 _ _ _ _ _ _ _ s | .BSload2_2 _ _ _ _ _ _ _ _ s
  | .BSloaddead _ _ _ _ _ s | .BSstore _ _ _ _ _ _ _ s
  | .BSstore2 _ _ _ _ _ _ _ _ _ _ s | .BScall _ _ _ _ _ _ _ s
  | .BSbuiltin _ _ _ _ _ _ _ s => [s]
  | .BStailcall .. => []
  | .BScond _ _ _ _ s1 s2 => [s1, s2]
  | .BSjumptable _ _ _ tbl => tbl
  | .BSreturn .. => []

/-- `Allocation.analyze`: `DS.fixpoint_allnodes` with
    `DS := Backward_Dataflow_Solver(LEq)(NodeSetBackward)`. -/
def analyze (win64 : Bool) (f : RTL.Function) (env : Regenv) (bsh : PTree BlockShape) :
    Option (PMap (Res Eqs)) :=
  Kildall.Backward.fixpointAllnodes (L := Res Eqs) (NS := NodeSetBackward) bsh
    successorsBlockShape (transfer win64 f env bsh)

/-- `Allocation.analyze` returns a solution of the backward dataflow
    inequations: the result at `n` contains what `transfer` requires before
    each successor `s` of `n`. -/
theorem analyze_solution (win64 : Bool) (f : RTL.Function) (env : Regenv)
    (bsh : PTree BlockShape) (res : PMap (Res Eqs)) (n : RTL.Node) (sh : BlockShape)
    (s : RTL.Node) (h : analyze win64 f env bsh = some res) (hc : bsh.get n = some sh)
    (hs : s ∈ successorsBlockShape sh) :
    LEq.ge (res.get n) (transfer win64 f env bsh s (res.get s)) :=
  Kildall.Backward.fixpointAllnodes_solution (L := Res Eqs) (NS := NodeSetBackward) bsh
    successorsBlockShape (transfer win64 f env bsh) res n sh s h hc hs

/-! ## Validating and translating functions and programs -/

/-- `Allocation.compat_entry` -/
def compatEntry : List Reg → List (RPair Loc) → Eqs → Bool
  | [], [], _ => true
  | r1 :: rl, .One l1 :: ll, e => compatLeft r1 l1 e && compatEntry rl ll e
  | r1 :: rl, .Twolong l1 l2 :: ll, e => compatLeft2 r1 l1 l2 e && compatEntry rl ll e
  | _, _, _ => false

/-- `Allocation.check_entrypoints_aux` -/
def checkEntrypointsAux (win64 : Bool) (rtl : RTL.Function) (ltl : LTL.Function)
    (env : Regenv) (e1 : Eqs) : Option Unit := do
  let mv ← pairEntrypoints rtl ltl
  let e2 ← trackMoves env mv e1
  if compatEntry rtl.fn_params (locParameters win64 rtl.fn_sig) e2 &&
      canUndef destroyedAtFunctionEntry e2 &&
      decide (rtl.fn_stacksize = ltl.fn_stacksize) && decide (rtl.fn_sig = ltl.fn_sig) then
    some ()
  else none

/-- `Allocation.check_entrypoints` -/
def checkEntrypoints (win64 : Bool) (rtl : RTL.Function) (ltl : LTL.Function) (env : Regenv)
    (bsh : PTree BlockShape) (a : PMap (Res Eqs)) : Res Unit := do
  let e1 ← transfer win64 rtl env bsh rtl.fn_entrypoint (a.get rtl.fn_entrypoint)
  match checkEntrypointsAux win64 rtl ltl env e1 with
  | none => .Error "invalid register allocation at entry point"
  | some _ => .OK ()

/-- `Allocation.check_function`: the validator. -/
def checkFunction (win64 : Bool) (rtl : RTL.Function) (ltl : LTL.Function) (env : Regenv) :
    Res Unit :=
  let bsh := pairCodes rtl ltl
  match analyze win64 rtl env bsh with
  | none => .Error "allocation analysis diverges"
  | some a => checkEntrypoints win64 rtl ltl env bsh a

section TRANSF
-- `regalloc`: the external register allocator (OCaml in Rocq).
variable (win64 : Bool) (regalloc : RTL.Function → Res LTL.Function)

/-- `Allocation.transf_function`: register allocation followed by validation. -/
def transfFunction (f : RTL.Function) : Res LTL.Function :=
  match RTLtyping.typeFunction win64 f with
  | .Error m => .Error m
  | .OK env =>
      match regalloc f with
      | .Error m => .Error m
      | .OK tf => do
          checkFunction win64 f tf env
          .OK tf

/-- `Allocation.transf_fundef` -/
def transfFundef (fd : RTL.Fundef) : Res LTL.Fundef :=
  ASTFundef.transfPartial (transfFunction win64 regalloc) fd

/-- `Allocation.transf_program` -/
def transfProgram (p : RTL.Program) : Res LTL.Program :=
  transformPartialProgram (transfFundef win64 regalloc) p

end TRANSF

end Allocation
end X86
end CC
