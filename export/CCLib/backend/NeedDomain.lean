/-
  Abstract domain for neededness analysis — port of `backend/NeedDomain.v`
  (definitions).

  Ported: `nval`, `iagree`, `lagree`, `vagree`, `eagree`, `nlub`,
  `complete_mask(64)`, the transfer functions on needs (`andimm`, `orimm`,
  `andlimm`, `orlimm`, `bitwise`, `shlimm`, `shruimm`, `shrimm`, `rol`,
  `ror`, `rolm`, `shllimm`, `shrluimm`, `shrlimm`, `roll`, `rorl`, `rolml`,
  `modarith`, `zero_ext`, `sign_ext`, `loword`, `hiword`, `makelong_lo`,
  `makelong_hi`, `longofintu`, `longofint`, `store_argument`, `maskzero`,
  `default`), the redundancy tests (`andimm_redundant`, …,
  `rolml_redundant`), the lattice `NVal`, the environments `NE`
  (`LPMap1(NVal)`), `nmem`, `nlive`, `nmem_all`, `nmem_add`,
  `nmem_remove`, `nmem_contains`, `nmem_dead_stack`, `nmem_lub`,
  `nmem_beq`, and the lattice `NA`.

  Differences from Rocq:
  * The lattices `NVal`, `NE`, `NA` are built with `Semilattice.free`
    (see `LatticeFree.lean`) from CompCert's `beq`/`bot`/`lub`; CompCert's
    orders (`nge`, the semantic order on `nmem`) and their lattice laws are
    not ported, nor are the soundness lemmas of the transfer functions.
  * `LPMap1.combine` is `PTree.combine` (they agree on every key).
  * `Val.lessdef v w` is spelled out as `v = w ∨ v = Vundef`.
-/
import CCLib.backend.ValueDomainMem
import CCLib.lib.IntvSets

namespace CC
namespace NeedDomain

open ValueDomain

abbrev I32 := Integers.Int
abbrev I64 := Integers.Int64

/-- `nval`: how much of a value is needed. -/
inductive Nval where
  /-- value is entirely unused -/
  | Nothing
  /-- only the bits that are 1 in `m` are needed (32-bit ints) -/
  | I (m : Integers.Int)
  /-- only the bits that are 1 in `m` are needed (64-bit ints) -/
  | L (m : Integers.Int64)
  /-- every bit of the value is used -/
  | All
  deriving DecidableEq, Inhabited

open Nval

/-- `iagree` -/
def iagree (p q mask : I32) : Prop :=
  ∀ i : Nat, i < 32 → Integers.Int.testbit mask i = true → Integers.Int.testbit p i = Integers.Int.testbit q i

/-- `lagree` -/
def lagree (p q mask : I64) : Prop :=
  ∀ i : Nat, i < 64 → Integers.Int64.testbit mask i = true → Integers.Int64.testbit p i = Integers.Int64.testbit q i

/-- `vagree v w x`: `w` agrees with `v` on the parts of `v` needed by `x`. -/
def vagree (v w : Val) (x : Nval) : Prop :=
  match x with
  | .Nothing => True
  | .I m =>
      match v, w with
      | .Vint p, .Vint q => iagree p q m
      | .Vint _, _ => False
      | _, _ => True
  | .L m =>
      match v, w with
      | .Vlong p, .Vlong q => lagree p q m
      | .Vlong _, _ => False
      | _, _ => True
  | .All => v = w ∨ v = .Vundef

/-- `nlub` -/
def nlub (x y : Nval) : Nval :=
  match x, y with
  | .Nothing, _ => y
  | _, .Nothing => x
  | .I m1, .I m2 => .I (Integers.Int.or m1 m2)
  | .L m1, .L m2 => .L (Integers.Int64.or m1 m2)
  | _, _ => .All

/-- `complete_mask` -/
def completeMask (m : I32) : I32 := Integers.Int.zero_ext (Integers.Int.size m).toNat Integers.Int.mone
/-- `complete_mask64` -/
def completeMask64 (m : I64) : I64 := Integers.Int64.zero_ext (Integers.Int64.size m).toNat Integers.Int64.mone

/-- `andimm` -/
def andimm (x : Nval) (n : I32) : Nval :=
  match x with
  | .Nothing => .Nothing
  | .I m => .I (Integers.Int.and m n)
  | _ => .I n

/-- `orimm` -/
def orimm (x : Nval) (n : I32) : Nval :=
  match x with
  | .Nothing => .Nothing
  | .I m => .I (Integers.Int.and m (Integers.Int.not n))
  | _ => .I (Integers.Int.not n)

/-- `andlimm` -/
def andlimm (x : Nval) (n : I64) : Nval :=
  match x with
  | .Nothing => .Nothing
  | .L m => .L (Integers.Int64.and m n)
  | _ => .L n

/-- `orlimm` -/
def orlimm (x : Nval) (n : I64) : Nval :=
  match x with
  | .Nothing => .Nothing
  | .L m => .L (Integers.Int64.and m (Integers.Int64.not n))
  | _ => .L (Integers.Int64.not n)

/-- `bitwise` -/
def bitwise (x : Nval) : Nval := x

/-- `shlimm` -/
def shlimm (x : Nval) (n : I32) : Nval :=
  match x with
  | .Nothing => .Nothing
  | .I m => .I (Integers.Int.shru m n)
  | _ => .I (Integers.Int.shru Integers.Int.mone n)

/-- `shruimm` -/
def shruimm (x : Nval) (n : I32) : Nval :=
  match x with
  | .Nothing => .Nothing
  | .I m => .I (Integers.Int.shl m n)
  | _ => .I (Integers.Int.shl Integers.Int.mone n)

/-- `shrimm` -/
def shrimm (x : Nval) (n : I32) : Nval :=
  match x with
  | .Nothing => .Nothing
  | .I m =>
      .I (let m' := Integers.Int.shl m n
          if Integers.Int.shru m' n = m then m' else Integers.Int.or m' (Integers.Int.repr Integers.Int.min_signed))
  | _ => .I (Integers.Int.or (Integers.Int.shl Integers.Int.mone n) (Integers.Int.repr Integers.Int.min_signed))

/-- `rol` -/
def rol (x : Nval) (amount : I32) : Nval :=
  match x with
  | .Nothing => .Nothing
  | .I m => .I (Integers.Int.ror m amount)
  | _ => .All

/-- `ror` -/
def ror (x : Nval) (amount : I32) : Nval :=
  match x with
  | .Nothing => .Nothing
  | .I m => .I (Integers.Int.rol m amount)
  | _ => .All

/-- `rolm` -/
def rolm (x : Nval) (amount mask : I32) : Nval := rol (andimm x mask) amount

/-- `shllimm` -/
def shllimm (x : Nval) (n : I32) : Nval :=
  match x with
  | .Nothing => .Nothing
  | .L m => .L (Integers.Int64.shru' m n)
  | _ => .L (Integers.Int64.shru' Integers.Int64.mone n)

/-- `shrluimm` -/
def shrluimm (x : Nval) (n : I32) : Nval :=
  match x with
  | .Nothing => .Nothing
  | .L m => .L (Integers.Int64.shl' m n)
  | _ => .L (Integers.Int64.shl' Integers.Int64.mone n)

/-- `shrlimm` -/
def shrlimm (x : Nval) (n : I32) : Nval :=
  match x with
  | .Nothing => .Nothing
  | .L m =>
      .L (let m' := Integers.Int64.shl' m n
          if Integers.Int64.shru' m' n = m then m' else Integers.Int64.or m' (Integers.Int64.repr Integers.Int64.min_signed))
  | _ => .L (Integers.Int64.or (Integers.Int64.shl' Integers.Int64.mone n) (Integers.Int64.repr Integers.Int64.min_signed))

/-- `roll` -/
def roll (x : Nval) (amount : I32) : Nval :=
  match x with
  | .Nothing => .Nothing
  | .L m => .L (Integers.Int64.ror m (Integers.Int64.repr (Integers.Int.unsigned amount)))
  | _ => .All

/-- `rorl` -/
def rorl (x : Nval) (amount : I32) : Nval :=
  match x with
  | .Nothing => .Nothing
  | .L m => .L (Integers.Int64.rol' m amount)
  | _ => .All

/-- `rolml` -/
def rolml (x : Nval) (amount : I32) (mask : I64) : Nval := roll (andlimm x mask) amount

/-- `modarith` -/
def modarith (x : Nval) : Nval :=
  match x with
  | .Nothing => .Nothing
  | .I m => .I (completeMask m)
  | .L m => .L (completeMask64 m)
  | .All => .All

/-- `zero_ext` -/
def zeroExt (n : Z) (x : Nval) : Nval :=
  match x with
  | .Nothing => .Nothing
  | .I m => .I (Integers.Int.zero_ext n.toNat m)
  | _ => .I (Integers.Int.zero_ext n.toNat Integers.Int.mone)

/-- `sign_ext` -/
def signExt (n : Z) (x : Nval) : Nval :=
  match x with
  | .Nothing => .Nothing
  | .I m => .I (Integers.Int.or (Integers.Int.zero_ext n.toNat m) (Integers.Int.shl Integers.Int.one (Integers.Int.repr (n - 1))))
  | _ => .I (Integers.Int.zero_ext n.toNat Integers.Int.mone)

/-- `loword` -/
def loword (x : Nval) : Nval :=
  match x with
  | .Nothing => .Nothing
  | .I m => .L (Integers.Int64.ofwords Integers.Int.zero m)
  | _ => .L (Integers.Int64.ofwords Integers.Int.zero Integers.Int.mone)

/-- `hiword` -/
def hiword (x : Nval) : Nval :=
  match x with
  | .Nothing => .Nothing
  | .I m => .L (Integers.Int64.ofwords m Integers.Int.zero)
  | _ => .L (Integers.Int64.ofwords Integers.Int.mone Integers.Int.zero)

/-- `makelong_lo` -/
def makelongLo (x : Nval) : Nval :=
  match x with
  | .Nothing => .Nothing
  | .L m => .I (Integers.Int64.loword m)
  | _ => .All

/-- `makelong_hi` -/
def makelongHi (x : Nval) : Nval :=
  match x with
  | .Nothing => .Nothing
  | .L m => .I (Integers.Int64.hiword m)
  | _ => .All

/-- `longofintu` -/
def longofintu (x : Nval) : Nval :=
  match x with
  | .Nothing => .Nothing
  | .L m => .I (Integers.Int64.loword m)
  | _ => .All

/-- `longofint` -/
def longofint (x : Nval) : Nval :=
  match x with
  | .Nothing => .Nothing
  | .L m => .I (Integers.Int.or (Integers.Int64.loword m) (Integers.Int.shl Integers.Int.one (Integers.Int.repr 31)))
  | _ => .All

/-- `store_argument` -/
def storeArgument (chunk : Chunk) : Nval :=
  match chunk with
  | .Mbool | .Mint8signed | .Mint8unsigned => .I (Integers.Int.repr 255)
  | .Mint16signed | .Mint16unsigned => .I (Integers.Int.repr 65535)
  | _ => .All

/-- `maskzero` -/
def maskzero (n : I32) : Nval := .I n

/-- `default` -/
def default (x : Nval) : Nval :=
  match x with
  | .Nothing => .Nothing
  | _ => .All

/-! ### Detecting operations that are redundant and can be turned into a move -/

/-- `andimm_redundant` -/
def andimmRedundant (x : Nval) (n : I32) : Bool :=
  match x with
  | .Nothing => true
  | .I m => decide (Integers.Int.and m (Integers.Int.not n) = Integers.Int.zero)
  | _ => false

/-- `orimm_redundant` -/
def orimmRedundant (x : Nval) (n : I32) : Bool :=
  match x with
  | .Nothing => true
  | .I m => decide (Integers.Int.and m n = Integers.Int.zero)
  | _ => false

/-- `rolm_redundant` -/
def rolmRedundant (x : Nval) (amount mask : I32) : Bool :=
  decide (amount = Integers.Int.zero) && andimmRedundant x mask

/-- `zero_ext_redundant` -/
def zeroExtRedundant (n : Z) (x : Nval) : Bool :=
  match x with
  | .Nothing => true
  | .I m => decide (Integers.Int.zero_ext n.toNat m = m)
  | _ => false

/-- `sign_ext_redundant` -/
def signExtRedundant (n : Z) (x : Nval) : Bool :=
  match x with
  | .Nothing => true
  | .I m => decide (Integers.Int.zero_ext n.toNat m = m)
  | _ => false

/-- `andlimm_redundant` -/
def andlimmRedundant (x : Nval) (n : I64) : Bool :=
  match x with
  | .Nothing => true
  | .L m => decide (Integers.Int64.and m (Integers.Int64.not n) = Integers.Int64.zero)
  | _ => false

/-- `orlimm_redundant` -/
def orlimmRedundant (x : Nval) (n : I64) : Bool :=
  match x with
  | .Nothing => true
  | .L m => decide (Integers.Int64.and m n = Integers.Int64.zero)
  | _ => false

/-- `rolml_redundant` -/
def rolmlRedundant (x : Nval) (amount : I32) (mask : I64) : Bool :=
  decide (amount = Integers.Int.zero) && andlimmRedundant x mask

/-! ### Lattices -/

/-- The semilattice `NVal`. -/
@[reducible] def NValLat : Semilattice Nval :=
  Semilattice.free (fun x y => decide (x = y)) .Nothing nlub

/-- `NE.t` (`LPMap1(NVal)`): absent registers are `Nothing`. -/
abbrev Nenv := PTree Nval

namespace NE
/-- `NE.get` -/
def get (p : Positive) (x : Nenv) : Nval := (x.get p).getD .Nothing
/-- `NE.set` -/
def set (p : Positive) (v : Nval) (x : Nenv) : Nenv :=
  if v = .Nothing then x.remove p else x.set p v
/-- `NE.beq` -/
def beq (x y : Nenv) : Bool := ptreeBeq (fun a b => decide (a = b)) x y
/-- `NE.bot` -/
def bot : Nenv := PTree.empty
/-- `LPMap1.opt_beq`-normalized lub of two optional needs. -/
def optLub (a b : Option Nval) : Option Nval :=
  match a, b with
  | none, none => none
  | some u, none => some u
  | none, some v => some v
  | some u, some v => some (nlub u v)
/-- `NE.lub` -/
def lub (x y : Nenv) : Nenv := PTree.combine optLub x y
/-- The semilattice `NE`. -/
@[reducible] def lat : Semilattice Nenv := Semilattice.free beq bot lub
end NE

/-- `nreg` -/
def nreg (ne : Nenv) (r : Reg) : Nval := NE.get r ne

/-- `eagree` -/
def eagree (e1 e2 : RTL.Regset) (ne : Nenv) : Prop :=
  ∀ r, vagree (e1.get r) (e2.get r) (NE.get r ne)

/-! ### Neededness for memory locations -/

/-- `nmem` -/
inductive Nmem where
  /-- all memory locations are dead (bottom) -/
  | NMemDead
  /-- all memory locations are live except the stack offsets in `stk`
      and the global offsets in the corresponding entry of `gl` -/
  | NMem (stk : ISet.T) (gl : PTree ISet.T)
  deriving Inhabited

open Nmem

/-- `nlive ge sp nm b ofs`: location `(b, ofs)` is live in `nm`. -/
def nlive {F V : Type} (ge : Genv F V) (sp : Block) : Nmem → Block → Z → Prop
  | .NMemDead, _, _ => False
  | .NMem stk gl, b, ofs =>
      (b = sp → ¬ ISet.In ofs stk) ∧
      (∀ id iv, Genv.findSymbol ge id = some b → gl.get id = some iv → ¬ ISet.In ofs iv)

/-- `nmem_all` -/
def nmemAll : Nmem := .NMem ISet.empty PTree.empty

/-- `Ptrofs.unsigned`, as used by the `nmem` operations. -/
def pu (o : Integers.Ptrofs) : Z := Integers.Ptrofs.unsigned o

/-- `nmem_add` -/
def nmemAdd (nm : Nmem) (p : Aptr) (sz : Z) : Nmem :=
  match nm with
  | .NMemDead => nmemAll
  | .NMem stk gl =>
      match p with
      | .Gl id ofs =>
          match gl.get id with
          | some iv => .NMem stk (gl.set id (ISet.remove (pu ofs) (pu ofs + sz) iv))
          | none => nm
      | .Glo id => .NMem stk (gl.remove id)
      | .Stk ofs => .NMem (ISet.remove (pu ofs) (pu ofs + sz) stk) gl
      | .Stack => .NMem ISet.empty gl
      | _ => nmemAll

/-- `nmem_remove` -/
def nmemRemove (nm : Nmem) (p : Aptr) (sz : Z) : Nmem :=
  match nm with
  | .NMemDead => .NMemDead
  | .NMem stk gl =>
      match p with
      | .Gl id ofs =>
          let iv' :=
            match gl.get id with
            | some iv => ISet.add (pu ofs) (pu ofs + sz) iv
            | none => ISet.interval (pu ofs) (pu ofs + sz)
          .NMem stk (gl.set id iv')
      | .Stk ofs => .NMem (ISet.add (pu ofs) (pu ofs + sz) stk) gl
      | _ => nm

/-- `nmem_contains` -/
def nmemContains (nm : Nmem) (p : Aptr) (sz : Z) : Bool :=
  match nm with
  | .NMemDead => false
  | .NMem stk gl =>
      match p with
      | .Gl id ofs =>
          match gl.get id with
          | some iv => !(ISet.contains (pu ofs) (pu ofs + sz) iv)
          | none => true
      | .Stk ofs => !(ISet.contains (pu ofs) (pu ofs + sz) stk)
      | _ => true

/-- `nmem_dead_stack` -/
def nmemDeadStack (sz : Z) : Nmem := .NMem (ISet.interval 0 sz) PTree.empty

/-- `nmem_lub` -/
def nmemLub (nm1 nm2 : Nmem) : Nmem :=
  match nm1, nm2 with
  | .NMemDead, _ => nm2
  | _, .NMemDead => nm1
  | .NMem stk1 gl1, .NMem stk2 gl2 =>
      .NMem (ISet.inter stk1 stk2)
        (PTree.combine (fun o1 o2 =>
            match o1, o2 with
            | some iv1, some iv2 => some (ISet.inter iv1 iv2)
            | _, _ => none) gl1 gl2)

/-- `nmem_beq` -/
def nmemBeq (nm1 nm2 : Nmem) : Bool :=
  match nm1, nm2 with
  | .NMemDead, .NMemDead => true
  | .NMem stk1 gl1, .NMem stk2 gl2 => ISet.beq stk1 stk2 && ptreeBeq ISet.beq gl1 gl2
  | _, _ => false

/-- `NA.t` -/
abbrev NAT := Nenv × Nmem

namespace NA
/-- `NA.beq` -/
def beq (x y : NAT) : Bool := NE.beq x.1 y.1 && nmemBeq x.2 y.2
/-- `NA.bot` -/
def bot : NAT := (NE.bot, .NMemDead)
/-- `NA.lub` -/
def lub (x y : NAT) : NAT := (NE.lub x.1 y.1, nmemLub x.2 y.2)
/-- The semilattice `NA` of the neededness analysis. -/
@[reducible] def lat : Semilattice NAT := Semilattice.free beq bot lub
end NA

end NeedDomain
end CC
