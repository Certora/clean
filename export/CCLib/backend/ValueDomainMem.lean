/-
  Abstract memory, abstract register environments and the dataflow
  lattice of the value analysis — port of the second half of
  `backend/ValueDomain.v`.

  Ported (definitions): `acontent`, `ablock`, `ablock_init`,
  `chunk_compat`, `ablock_load`, `ablock_load_anywhere`, `inval_after`,
  `inval_if`, `inval_before`, `ablock_store`, `ablock_store_anywhere`,
  `ablock_loadbytes`, `ablock_storebytes`, `ablock_storebytes_anywhere`,
  `smatch`, `bmatch`, `bbeq`, `combine_acontents`, `blub`, `romem`,
  `romatch`, `amem`, `mmatch`, `minit`, `mbot`, `mtop`, `load`, `loadv`,
  `store`, `storev`, `loadbytes`, `storebytes`, `mbeq`, `combine_ablock`,
  `mlub`, the lattice `AVal`, the environments `AE` (`LPMap(AVal)` from
  `lib/Lattice.v`: `get`, `set`, `beq`, `bot`, `top`, `lub`), `aenv`,
  `ematch`, `einit_regs`, `eforget`, and the lattice `VA`.
  Also `CountedLoop.up` (from `lib/Iteration.v`), `ZTree` (from
  `lib/Maps.v`) and `PTree.beq`.

  Differences from Rocq:
  * `Compopts.va_strict` is an explicit argument `strict`; `Archi.abi`
    (used by `einit_regs`) is an explicit argument `abi`.
  * The lattice structures `AVal`, `AE` and `VA` are built with
    `Semilattice.free` (see `LatticeFree.lean`): the computational content
    (`beq`, `bot`, `lub`) is CompCert's, but the order is the one generated
    by these operations rather than `vge` / the semantic order of `VA.ge`
    (whose lattice laws are not proved here).
  * `LPMap1.combine` (a version of `PTree.combine` that shares unchanged
    subtrees) is `PTree.combine`; the two agree on every key.
  * `ZTree` is a `PTree` indexed through `ZIndexed.index`.
-/
import CCLib.backend.ValueDomain
import CCLib.lib.LatticeFree
import CCLib.lib.MapsTheory
import CCLib.backend.RTL

namespace CC
namespace ValueDomain

/-! ## Auxiliary structures -/

/-- `Iteration.CountedLoop.up f lo hi a` = `a |> f lo |> … |> f (hi-1)`. -/
def countedUp {A : Type} (f : Z → A → A) (lo hi : Z) (a : A) : A :=
  go (hi - lo).toNat lo a
where
  go : Nat → Z → A → A
    | 0, _, a => a
    | n + 1, i, a => go n (i + 1) (f i a)

/-- `PTree.beq`: same keys, and `cmp` holds on the values of each key. -/
def ptreeBeq {A : Type} (cmp : A → A → Bool) : PTree A → PTree A → Bool
  | .Leaf, .Leaf => true
  | .Leaf, .Node l o r => o.isNone && ptreeBeq cmp .Leaf l && ptreeBeq cmp .Leaf r
  | .Node l o r, .Leaf => o.isNone && ptreeBeq cmp l .Leaf && ptreeBeq cmp r .Leaf
  | .Node l1 o1 r1, .Node l2 o2 r2 =>
      (match o1, o2 with
       | none, none => true
       | some x, some y => cmp x y
       | _, _ => false) && ptreeBeq cmp l1 l2 && ptreeBeq cmp r1 r2

/-- `Maps.ZTree`: finite maps indexed by integers. -/
abbrev ZTree (A : Type) := PTree A

namespace ZTree
def empty {A : Type} : ZTree A := PTree.empty
def get {A : Type} (i : Z) (m : ZTree A) : Option A := PTree.get (ZIndexed.index i) m
def set {A : Type} (i : Z) (v : A) (m : ZTree A) : ZTree A := PTree.set (ZIndexed.index i) v m
def remove {A : Type} (i : Z) (m : ZTree A) : ZTree A := PTree.remove (ZIndexed.index i) m
end ZTree

/-! ## Abstracting memory blocks -/

/-- `ValueDomain.acontent` -/
inductive Acontent where
  | ACval (chunk : Chunk) (av : Aval)
  deriving DecidableEq, Repr

/-- `ValueDomain.ablock` -/
structure Ablock where
  ab_contents : ZTree Acontent
  ab_summary : Aptr

instance : Inhabited Ablock := ⟨⟨.Leaf, .Pbot⟩⟩

/-- `ValueDomain.ablock_init` -/
def ablockInit (p : Aptr) : Ablock := { ab_contents := ZTree.empty, ab_summary := p }

/-- `ValueDomain.chunk_compat` -/
def chunkCompat (chunk chunk' : Chunk) : Bool :=
  match chunk, chunk' with
  | .Mint8signed, .Mint8signed | .Mint8signed, .Mint8unsigned
  | .Mint8unsigned, .Mint8signed | .Mint8unsigned, .Mint8unsigned => true
  | .Mint16signed, .Mint16signed | .Mint16signed, .Mint16unsigned
  | .Mint16unsigned, .Mint16signed | .Mint16unsigned, .Mint16unsigned => true
  | .Mint32, .Mint32 => true
  | .Mfloat32, .Mfloat32 => true
  | .Mint64, .Mint64 => true
  | .Mfloat64, .Mfloat64 => true
  | .Many32, .Many32 => true
  | .Many64, .Many64 => true
  | _, _ => false

/-- `ValueDomain.ablock_load` -/
def ablockLoad (chunk : Chunk) (ab : Ablock) (i : Z) : Aval :=
  match ZTree.get i ab.ab_contents with
  | none => vnormalize chunk (.Ifptr ab.ab_summary)
  | some (.ACval chunk' av) =>
      if chunkCompat chunk chunk' then vnormalize chunk av
      else vnormalize chunk (.Ifptr ab.ab_summary)

/-- `ValueDomain.ablock_load_anywhere` -/
def ablockLoadAnywhere (chunk : Chunk) (ab : Ablock) : Aval :=
  vnormalize chunk (.Ifptr ab.ab_summary)

/-- `ValueDomain.inval_after` -/
def invalAfter (lo hi : Z) (c : ZTree Acontent) : ZTree Acontent :=
  countedUp (fun i c => ZTree.remove i c) lo hi c

/-- `ValueDomain.inval_if` -/
def invalIf (hi lo : Z) (c : ZTree Acontent) : ZTree Acontent :=
  match ZTree.get lo c with
  | none => c
  | some (.ACval chunk _) => if lo + sizeChunk chunk ≤ hi then c else ZTree.remove lo c

/-- `ValueDomain.inval_before` -/
def invalBefore (hi lo : Z) (c : ZTree Acontent) : ZTree Acontent :=
  countedUp (invalIf hi) lo hi c

/-- `ValueDomain.ablock_store` -/
def ablockStore (chunk : Chunk) (ab : Ablock) (i : Z) (av : Aval) : Ablock :=
  { ab_contents :=
      ZTree.set i (.ACval chunk av)
        (invalBefore i (i - 7) (invalAfter (i + 1) (i + sizeChunk chunk) ab.ab_contents))
    ab_summary := vplub av ab.ab_summary }

/-- `ValueDomain.ablock_store_anywhere` -/
def ablockStoreAnywhere (_chunk : Chunk) (ab : Ablock) (av : Aval) : Ablock :=
  ablockInit (vplub av ab.ab_summary)

/-- `ValueDomain.ablock_loadbytes` -/
def ablockLoadbytes (ab : Ablock) : Aptr := ab.ab_summary

/-- `ValueDomain.ablock_storebytes` -/
def ablockStorebytes (ab : Ablock) (p : Aptr) (ofs sz : Z) : Ablock :=
  { ab_contents := invalBefore ofs (ofs - 7) (invalAfter ofs (ofs + sz) ab.ab_contents)
    ab_summary := plub p ab.ab_summary }

/-- `ValueDomain.ablock_storebytes_anywhere` -/
def ablockStorebytesAnywhere (ab : Ablock) (p : Aptr) : Ablock :=
  ablockInit (plub p ab.ab_summary)

section MATCH
variable (bc : BlockClassification)

/-- `ValueDomain.smatch` -/
def Smatch (m : Mem) (b : Block) (p : Aptr) : Prop :=
  (∀ chunk ofs v, Mem.load chunk m b ofs = some v → Vmatch bc v (.Ifptr p)) ∧
  (∀ ofs b' ofs' q i, Mem.loadbytes m b ofs 1 = some [.Fragment (.Vptr b' ofs') q i] →
    Pmatch bc b' ofs' p)

/-- `ValueDomain.bmatch` -/
def Bmatch (m : Mem) (b : Block) (ab : Ablock) : Prop :=
  Smatch bc m b ab.ab_summary ∧
  ∀ chunk ofs v, Mem.load chunk m b ofs = some v → Vmatch bc v (ablockLoad chunk ab ofs)

end MATCH

/-- `ValueDomain.bbeq` -/
def bbeq (ab1 ab2 : Ablock) : Bool :=
  decide (ab1.ab_summary = ab2.ab_summary) &&
  ptreeBeq (fun c1 c2 => decide (c1 = c2)) ab1.ab_contents ab2.ab_contents

section STRICT
variable (strict : Bool)

/-- `ValueDomain.combine_acontents` -/
def combineAcontents (c1 c2 : Option Acontent) : Option Acontent :=
  match c1, c2 with
  | some (.ACval chunk1 v1), some (.ACval chunk2 v2) =>
      if chunk1 = chunk2 then some (.ACval chunk1 (vlub strict v1 v2)) else none
  | _, _ => none

/-- `ValueDomain.blub` -/
def blub (ab1 ab2 : Ablock) : Ablock :=
  { ab_contents := PTree.combine (combineAcontents strict) ab1.ab_contents ab2.ab_contents
    ab_summary := plub ab1.ab_summary ab2.ab_summary }

end STRICT

/-! ## Read-only global variables and abstract memory states -/

/-- `ValueDomain.romem` -/
abbrev Romem := PTree Ablock

/-- `ValueDomain.romatch` -/
def Romatch (bc : BlockClassification) (m : Mem) (rm : Romem) : Prop :=
  ∀ b id ab, bc b = .BCglob id → rm.get id = some ab →
    Pge .Glob ab.ab_summary ∧ Bmatch bc m b ab ∧
    ∀ ofs, Mem.perm m b ofs .Max .Writable = false

/-- `ValueDomain.amem` -/
structure Amem where
  am_stack : Ablock
  am_glob : PTree Ablock
  am_nonstack : Aptr
  am_top : Aptr

instance : Inhabited Amem := ⟨⟨default, .Leaf, .Pbot, .Pbot⟩⟩

/-- `ValueDomain.mmatch` -/
structure Mmatch (bc : BlockClassification) (m : Mem) (am : Amem) : Prop where
  mmatch_stack : ∀ b, bc b = .BCstack → Bmatch bc m b am.am_stack
  mmatch_glob : ∀ id ab b, bc b = .BCglob id → am.am_glob.get id = some ab → Bmatch bc m b ab
  mmatch_nonstack : ∀ b, bc b ≠ .BCstack → bc b ≠ .BCinvalid → Smatch bc m b am.am_nonstack
  mmatch_top : ∀ b, bc b ≠ .BCinvalid → Smatch bc m b am.am_top
  mmatch_below : bcBelow bc m.nextblock

/-- `ValueDomain.minit` -/
def minit (p : Aptr) : Amem :=
  { am_stack := ablockInit p, am_glob := PTree.empty, am_nonstack := p, am_top := p }

/-- `ValueDomain.mbot` -/
def mbot : Amem := minit .Pbot
/-- `ValueDomain.mtop` -/
def mtop : Amem := minit .Ptop

section STRICT
variable (strict : Bool)

/-- `ValueDomain.load` -/
def load (chunk : Chunk) (rm : Romem) (m : Amem) (p : Aptr) : Aval :=
  match p with
  | .Pbot => if strict then .Vbot else Vtop
  | .Gl id ofs =>
      match rm.get id with
      | some ab => ablockLoad chunk ab (Integers.Ptrofs.unsigned ofs)
      | none =>
          match m.am_glob.get id with
          | some ab => ablockLoad chunk ab (Integers.Ptrofs.unsigned ofs)
          | none => vnormalize chunk (.Ifptr m.am_nonstack)
  | .Glo id =>
      match rm.get id with
      | some ab => ablockLoadAnywhere chunk ab
      | none =>
          match m.am_glob.get id with
          | some ab => ablockLoadAnywhere chunk ab
          | none => vnormalize chunk (.Ifptr m.am_nonstack)
  | .Stk ofs => ablockLoad chunk m.am_stack (Integers.Ptrofs.unsigned ofs)
  | .Stack => ablockLoadAnywhere chunk m.am_stack
  | .Glob | .Nonstack => vnormalize chunk (.Ifptr m.am_nonstack)
  | .Ptop => vnormalize chunk (.Ifptr m.am_top)

/-- `ValueDomain.loadv` -/
def loadv (chunk : Chunk) (rm : Romem) (m : Amem) (addr : Aval) : Aval :=
  load strict chunk rm m (aptrOfAval strict addr)

end STRICT

/-- The abstract block of global `id` (or the default non-stack block). -/
def globBlock (m : Amem) (id : Ident) : Ablock :=
  match m.am_glob.get id with
  | some ab => ab
  | none => ablockInit m.am_nonstack

/-- `ValueDomain.store` -/
def store (chunk : Chunk) (m : Amem) (p : Aptr) (av : Aval) : Amem :=
  { am_stack :=
      match p with
      | .Stk ofs => ablockStore chunk m.am_stack (Integers.Ptrofs.unsigned ofs) av
      | .Stack | .Ptop => ablockStoreAnywhere chunk m.am_stack av
      | _ => m.am_stack
    am_glob :=
      match p with
      | .Gl id ofs =>
          m.am_glob.set id (ablockStore chunk (globBlock m id) (Integers.Ptrofs.unsigned ofs) av)
      | .Glo id => m.am_glob.set id (ablockStoreAnywhere chunk (globBlock m id) av)
      | .Glob | .Nonstack | .Ptop => PTree.empty
      | _ => m.am_glob
    am_nonstack :=
      match p with
      | .Gl _ _ | .Glo _ | .Glob | .Nonstack | .Ptop => vplub av m.am_nonstack
      | _ => m.am_nonstack
    am_top := vplub av m.am_top }

/-- `ValueDomain.storev` -/
def storev (strict : Bool) (chunk : Chunk) (m : Amem) (addr v : Aval) : Amem :=
  store chunk m (aptrOfAval strict addr) v

/-- `ValueDomain.loadbytes` -/
def loadbytes (strict : Bool) (m : Amem) (rm : Romem) (p : Aptr) : Aptr :=
  match p with
  | .Pbot => if strict then .Pbot else .Ptop
  | .Gl id _ | .Glo id =>
      match rm.get id with
      | some ab => ablockLoadbytes ab
      | none =>
          match m.am_glob.get id with
          | some ab => ablockLoadbytes ab
          | none => m.am_nonstack
  | .Stk _ | .Stack => ablockLoadbytes m.am_stack
  | .Glob | .Nonstack => m.am_nonstack
  | .Ptop => m.am_top

/-- `ValueDomain.storebytes` -/
def storebytes (m : Amem) (dst : Aptr) (sz : Z) (p : Aptr) : Amem :=
  { am_stack :=
      match dst with
      | .Stk ofs => ablockStorebytes m.am_stack p (Integers.Ptrofs.unsigned ofs) sz
      | .Stack | .Ptop => ablockStorebytesAnywhere m.am_stack p
      | _ => m.am_stack
    am_glob :=
      match dst with
      | .Gl id ofs =>
          m.am_glob.set id (ablockStorebytes (globBlock m id) p (Integers.Ptrofs.unsigned ofs) sz)
      | .Glo id => m.am_glob.set id (ablockStorebytesAnywhere (globBlock m id) p)
      | .Glob | .Nonstack | .Ptop => PTree.empty
      | _ => m.am_glob
    am_nonstack :=
      match dst with
      | .Gl _ _ | .Glo _ | .Glob | .Nonstack | .Ptop => plub p m.am_nonstack
      | _ => m.am_nonstack
    am_top := plub p m.am_top }

/-- `ValueDomain.mbeq` -/
def mbeq (m1 m2 : Amem) : Bool :=
  decide (m1.am_top = m2.am_top) && decide (m1.am_nonstack = m2.am_nonstack) &&
  bbeq m1.am_stack m2.am_stack && ptreeBeq bbeq m1.am_glob m2.am_glob

section STRICT
variable (strict : Bool)

/-- `ValueDomain.combine_ablock` -/
def combineAblock (ob1 ob2 : Option Ablock) : Option Ablock :=
  match ob1, ob2 with
  | some b1, some b2 => some (blub strict b1 b2)
  | _, _ => none

/-- `ValueDomain.mlub` -/
def mlub (m1 m2 : Amem) : Amem :=
  { am_stack := blub strict m1.am_stack m2.am_stack
    am_glob := PTree.combine (combineAblock strict) m1.am_glob m2.am_glob
    am_nonstack := plub m1.am_nonstack m2.am_nonstack
    am_top := plub m1.am_top m2.am_top }

/-! ## Abstracting RTL register environments -/

/-- `ValueDomain.AVal`: the semilattice of abstract values (bottom `Vbot`,
    top `Vtop`, join `vlub`). -/
@[reducible] def AValLat : Semilattice Aval :=
  Semilattice.free (fun x y => decide (x = y)) .Vbot (vlub strict)

end STRICT

/-- `ValueDomain.AE.t` (`LPMap(AVal).t`): `Bot`, or a map whose missing
    entries are `Vtop`. -/
inductive Aenv where
  | Bot
  | Top_except (m : PTree Aval)

instance : Inhabited Aenv := ⟨.Bot⟩

namespace AE

/-- `AE.get` -/
def get (p : Positive) (x : Aenv) : Aval :=
  match x with
  | .Bot => .Vbot
  | .Top_except m =>
      match m.get p with
      | none => Vtop
      | some x => x

/-- `AE.set` -/
def set (p : Positive) (v : Aval) (x : Aenv) : Aenv :=
  match x with
  | .Bot => .Bot
  | .Top_except m =>
      if v = .Vbot then .Bot
      else .Top_except (if v = Vtop then m.remove p else m.set p v)

/-- `AE.beq` -/
def beq (x y : Aenv) : Bool :=
  match x, y with
  | .Bot, .Bot => true
  | .Top_except m, .Top_except n => ptreeBeq (fun a b => decide (a = b)) m n
  | _, _ => false

/-- `AE.bot` -/
def bot : Aenv := .Bot
/-- `AE.top` -/
def top : Aenv := .Top_except PTree.empty

/-- `LPMap.opt_lub` -/
def optLub (strict : Bool) (x y : Aval) : Option Aval :=
  let z := vlub strict x y
  if z = Vtop then none else some z

/-- `AE.lub` -/
def lub (strict : Bool) (x y : Aenv) : Aenv :=
  match x, y with
  | .Bot, _ => y
  | _, .Bot => x
  | .Top_except m, .Top_except n =>
      .Top_except (PTree.combine (fun a b =>
        match a, b with
        | some u, some v => optLub strict u v
        | _, _ => none) m n)

/-- The semilattice `AE` of abstract register environments. -/
@[reducible] def lat (strict : Bool) : Semilattice Aenv := Semilattice.free beq bot (lub strict)

end AE

/-- `ValueDomain.aenv` -/
abbrev AenvT := Aenv

/-- `ValueDomain.ematch` -/
def Ematch (bc : BlockClassification) (e : RTL.Regset) (ae : Aenv) : Prop :=
  ∀ r, Vmatch bc (PMap.get r e) (AE.get r ae)

/-- `ValueDomain.einit_regs` -/
def einitRegs (abi : Conventions1.AbiKind) : List Reg → List XType → Aenv
  | [], _ => AE.top
  | r1 :: rs, t1 :: ts =>
      let a1 := if Conventions1.parameterNeedsNormalization abi t1 then .Ifptr .Nonstack
        else ofXtype t1 .Nonstack
      AE.set r1 a1 (einitRegs abi rs ts)
  | r1 :: rs, [] => AE.set r1 (.Ifptr .Nonstack) (einitRegs abi rs [])

/-- `ValueDomain.eforget` -/
def eforget : List Reg → Aenv → Aenv
  | [], ae => ae
  | r1 :: rs, ae => eforget rs (AE.set r1 Vtop ae)

/-! ## The lattice for dataflow analysis -/

/-- `ValueDomain.VA.t` -/
inductive VAState where
  | Bot
  | State (ae : Aenv) (am : Amem)

instance : Inhabited VAState := ⟨.Bot⟩

namespace VA

/-- `VA.beq` -/
def beq (x y : VAState) : Bool :=
  match x, y with
  | .Bot, .Bot => true
  | .State ae1 am1, .State ae2 am2 => AE.beq ae1 ae2 && mbeq am1 am2
  | _, _ => false

/-- `VA.bot` -/
def bot : VAState := .Bot

/-- `VA.lub` -/
def lub (strict : Bool) (x y : VAState) : VAState :=
  match x, y with
  | .Bot, _ => y
  | _, .Bot => x
  | .State ae1 am1, .State ae2 am2 => .State (AE.lub strict ae1 ae2) (mlub strict am1 am2)

/-- The semilattice `VA`. -/
@[reducible] def lat (strict : Bool) : Semilattice VAState := Semilattice.free beq bot (lub strict)

end VA

end ValueDomain
end CC
