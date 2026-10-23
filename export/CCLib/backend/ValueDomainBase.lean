/-
  First part of the port of `backend/ValueDomain.v` (split from `CCLib.backend.ValueDomain`): block classifications, abstract booleans, abstract pointers and abstract values, with their matching relations and lattice operations.
-/
import CCLib.common.Memory
import CCLib.common.Globalenvs
import CCLib.aarch64.Conventions1

namespace CC
namespace ValueDomain

/-! ## Block classification -/

/-- `ValueDomain.block_class` -/
inductive BlockClass where
  | BCinvalid
  | BCglob (id : Ident)
  | BCstack
  | BCother
  deriving DecidableEq, Repr

/-- `ValueDomain.block_classification` -/
structure BlockClassification where
  bc_img : Block → BlockClass
  bc_stack : ∀ b1 b2, bc_img b1 = .BCstack → bc_img b2 = .BCstack → b1 = b2
  bc_glob : ∀ b1 b2 id, bc_img b1 = .BCglob id → bc_img b2 = .BCglob id → b1 = b2

instance : CoeFun BlockClassification (fun _ => Block → BlockClass) := ⟨BlockClassification.bc_img⟩

/-- `ValueDomain.bc_below` -/
def bcBelow (bc : BlockClassification) (bound : Block) : Prop :=
  ∀ b, bc b ≠ .BCinvalid → b < bound

/-! ## Abstract booleans (results of conditions) -/

/-- `ValueDomain.abool` -/
inductive Abool where
  /-- always `None` (undefined) -/
  | Bnone
  /-- always `Some b` -/
  | Just (b : Bool)
  /-- either `None` or `Some b` -/
  | Maybe (b : Bool)
  /-- unknown -/
  | Btop
  deriving DecidableEq, Repr

/-- `ValueDomain.cmatch` -/
inductive Cmatch : Option Bool → Abool → Prop where
  | none : Cmatch none .Bnone
  | just (b) : Cmatch (some b) (.Just b)
  | maybe_none (b) : Cmatch none (.Maybe b)
  | maybe_some (b) : Cmatch (some b) (.Maybe b)
  | top (ob) : Cmatch ob .Btop

/-- `ValueDomain.club` -/
def club (x y : Abool) : Abool :=
  match x, y with
  | .Bnone, .Bnone => .Bnone
  | .Bnone, .Just b | .Bnone, .Maybe b => .Maybe b
  | .Just b, .Bnone | .Maybe b, .Bnone => .Maybe b
  | .Just b1, .Just b2 => if b1 == b2 then x else .Btop
  | .Maybe b1, .Maybe b2 => if b1 == b2 then x else .Btop
  | .Maybe b1, .Just b2 => if b1 == b2 then x else .Btop
  | .Just b1, .Maybe b2 => if b1 == b2 then y else .Btop
  | _, _ => .Btop

theorem cmatch_lub_l {ob : Option Bool} {x : Abool} (y : Abool) (h : Cmatch ob x) :
    Cmatch ob (club x y) := by
  cases h <;> cases y <;> simp only [club] <;>
    first
    | constructor
    | (split <;> rename_i h <;> (try simp at h) <;> (try subst h) <;> constructor)

theorem cmatch_lub_r {ob : Option Bool} (x : Abool) {y : Abool} (h : Cmatch ob y) :
    Cmatch ob (club x y) := by
  cases h <;> cases x <;> simp only [club] <;>
    first
    | constructor
    | (split <;> rename_i h <;> (try simp at h) <;> (try subst h) <;> constructor)

/-- `ValueDomain.cnot` -/
def cnot (x : Abool) : Abool :=
  match x with
  | .Just b => .Just (!b)
  | .Maybe b => .Maybe (!b)
  | _ => x

theorem cnot_sound {ob : Option Bool} {x : Abool} (h : Cmatch ob x) :
    Cmatch (ob.map not) (cnot x) := by
  cases h <;> constructor

/-! ## Abstract pointers -/

/-- `ValueDomain.aptr` -/
inductive Aptr where
  /-- empty set of pointers -/
  | Pbot
  /-- into the block of global `id` at offset `ofs` -/
  | Gl (id : Ident) (ofs : Integers.Ptrofs)
  /-- anywhere into the block of global `id` -/
  | Glo (id : Ident)
  /-- into any global variable -/
  | Glob
  /-- into the current stack frame at offset `ofs` -/
  | Stk (ofs : Integers.Ptrofs)
  /-- anywhere into the current stack frame -/
  | Stack
  /-- anywhere but into the current stack frame -/
  | Nonstack
  /-- any valid pointer -/
  | Ptop
  deriving DecidableEq, Repr

section MATCH
variable (bc : BlockClassification)

/-- `ValueDomain.pmatch` -/
inductive Pmatch (b : Block) (ofs : Integers.Ptrofs) : Aptr → Prop where
  | gl (id) : bc b = .BCglob id → Pmatch b ofs (.Gl id ofs)
  | glo (id) : bc b = .BCglob id → Pmatch b ofs (.Glo id)
  | glob (id) : bc b = .BCglob id → Pmatch b ofs .Glob
  | stk : bc b = .BCstack → Pmatch b ofs (.Stk ofs)
  | stack : bc b = .BCstack → Pmatch b ofs .Stack
  | nonstack : bc b ≠ .BCstack → bc b ≠ .BCinvalid → Pmatch b ofs .Nonstack
  | top : bc b ≠ .BCinvalid → Pmatch b ofs .Ptop

end MATCH

/-- `ValueDomain.pge` -/
inductive Pge : Aptr → Aptr → Prop where
  | top (p) : Pge .Ptop p
  | bot (p) : Pge p .Pbot
  | refl (p) : Pge p p
  | glo_gl (id ofs) : Pge (.Glo id) (.Gl id ofs)
  | glob_gl (id ofs) : Pge .Glob (.Gl id ofs)
  | glob_glo (id) : Pge .Glob (.Glo id)
  | ns_gl (id ofs) : Pge .Nonstack (.Gl id ofs)
  | ns_glo (id) : Pge .Nonstack (.Glo id)
  | ns_glob : Pge .Nonstack .Glob
  | stack_stk (ofs) : Pge .Stack (.Stk ofs)

/-- `ValueDomain.pge_trans` -/
theorem pge_trans {p q r : Aptr} (h1 : Pge p q) (h2 : Pge q r) : Pge p r := by
  cases h1 <;> cases h2 <;> constructor

/-- `ValueDomain.pmatch_ge` -/
theorem pmatch_ge {bc : BlockClassification} {b : Block} {ofs : Integers.Ptrofs} {p q : Aptr}
    (hge : Pge p q) (hm : Pmatch bc b ofs q) : Pmatch bc b ofs p := by
  have nonstack_of_glob : ∀ id, bc b = .BCglob id → Pmatch bc b ofs .Nonstack := fun id h =>
    .nonstack (by rw [h]; simp) (by rw [h]; simp)
  cases hge with
  | top =>
      apply Pmatch.top
      cases hm <;> (try (rename_i h; rw [h]; simp)) <;> assumption
  | bot => cases hm
  | refl => exact hm
  | glo_gl => cases hm with | gl _ h => exact .glo _ h
  | glob_gl => cases hm with | gl _ h => exact .glob _ h
  | glob_glo => cases hm with | glo _ h => exact .glob _ h
  | ns_gl => cases hm with | gl _ h => exact nonstack_of_glob _ h
  | ns_glo => cases hm with | glo _ h => exact nonstack_of_glob _ h
  | ns_glob => cases hm with | glob _ h => exact nonstack_of_glob _ h
  | stack_stk => cases hm with | stk h => exact .stack h

/-- `ValueDomain.plub` -/
def plub (p q : Aptr) : Aptr :=
  match p, q with
  | .Pbot, _ => q
  | _, .Pbot => p
  | .Gl id1 ofs1, .Gl id2 ofs2 =>
      if id1 = id2 then (if ofs1 = ofs2 then p else .Glo id1) else .Glob
  | .Gl id1 _, .Glo id2 => if id1 = id2 then q else .Glob
  | .Glo id1, .Gl id2 _ => if id1 = id2 then p else .Glob
  | .Glo id1, .Glo id2 => if id1 = id2 then p else .Glob
  | .Gl _ _, .Glob | .Glo _, .Glob | .Glob, .Glob => .Glob
  | .Glob, .Gl _ _ | .Glob, .Glo _ => .Glob
  | .Gl _ _, .Nonstack | .Glo _, .Nonstack | .Glob, .Nonstack | .Nonstack, .Nonstack => .Nonstack
  | .Nonstack, .Gl _ _ | .Nonstack, .Glo _ | .Nonstack, .Glob => .Nonstack
  | .Stk ofs1, .Stk ofs2 => if ofs1 = ofs2 then p else .Stack
  | .Stk _, .Stack | .Stack, .Stack => .Stack
  | .Stack, .Stk _ => .Stack
  | _, _ => .Ptop

/-- `ValueDomain.pincl` -/
def pincl (p q : Aptr) : Bool :=
  match p, q with
  | .Pbot, _ => true
  | .Gl id1 ofs1, .Gl id2 ofs2 => decide (id1 = id2) && decide (ofs1 = ofs2)
  | .Gl id1 _, .Glo id2 => decide (id1 = id2)
  | .Glo id1, .Glo id2 => decide (id1 = id2)
  | .Gl _ _, .Glob | .Glo _, .Glob | .Glob, .Glob => true
  | .Gl _ _, .Nonstack | .Glo _, .Nonstack | .Glob, .Nonstack | .Nonstack, .Nonstack => true
  | .Stk ofs1, .Stk ofs2 => decide (ofs1 = ofs2)
  | .Stk _, .Stack => true
  | .Stack, .Stack => true
  | _, .Ptop => true
  | _, _ => false

/-- `ValueDomain.padd` -/
def padd (p : Aptr) (n : Integers.Ptrofs) : Aptr :=
  match p with
  | .Gl id ofs => .Gl id (Integers.Ptrofs.add ofs n)
  | .Stk ofs => .Stk (Integers.Ptrofs.add ofs n)
  | _ => p

/-- `ValueDomain.psub` -/
def psub (p : Aptr) (n : Integers.Ptrofs) : Aptr :=
  match p with
  | .Gl id ofs => .Gl id (Integers.Ptrofs.sub ofs n)
  | .Stk ofs => .Stk (Integers.Ptrofs.sub ofs n)
  | _ => p

/-- `ValueDomain.poffset` -/
def poffset (p : Aptr) : Aptr :=
  match p with
  | .Gl id _ => .Glo id
  | .Stk _ => .Stack
  | _ => p

section STRICT
variable (strict : Bool)

/-- `ValueDomain.cmp_different_blocks` -/
def cmpDifferentBlocks (c : Comparison) : Abool :=
  match c with
  | .Ceq => .Maybe false
  | .Cne => .Maybe true
  | _ => if strict then .Bnone else .Btop

/-- `ValueDomain.pcmp` -/
def pcmp (c : Comparison) (p1 p2 : Aptr) : Abool :=
  match p1, p2 with
  | .Pbot, _ | _, .Pbot => .Bnone
  | .Gl id1 ofs1, .Gl id2 ofs2 =>
      if id1 = id2 then .Maybe (Integers.Ptrofs.cmpu c ofs1 ofs2) else .Btop
  | .Stk ofs1, .Stk ofs2 => .Maybe (Integers.Ptrofs.cmpu c ofs1 ofs2)
  | .Gl _ _, .Stk _ | .Glo _, .Stk _ | .Glob, .Stk _ | .Nonstack, .Stk _
  | .Gl _ _, .Stack | .Glo _, .Stack | .Glob, .Stack | .Nonstack, .Stack =>
      cmpDifferentBlocks strict c
  | .Stk _, .Gl _ _ | .Stk _, .Glo _ | .Stk _, .Glob | .Stk _, .Nonstack
  | .Stack, .Gl _ _ | .Stack, .Glo _ | .Stack, .Glob | .Stack, .Nonstack =>
      cmpDifferentBlocks strict c
  | _, _ => .Btop

end STRICT

/-! ## Abstract values -/

/-- `ValueDomain.aval` -/
inductive Aval where
  /-- empty set of values -/
  | Vbot
  /-- exactly `Vint n` -/
  | I (n : Integers.Int)
  /-- `Vint n` or `Vundef` -/
  | IU (n : Integers.Int)
  /-- an `n`-bit unsigned integer, or `Vundef` -/
  | Uns (p : Aptr) (n : Z)
  /-- an `n`-bit signed integer, or `Vundef` -/
  | Sgn (p : Aptr) (n : Z)
  /-- exactly `Vlong n` -/
  | L (n : Integers.Int64)
  /-- exactly `Vfloat f` -/
  | F (f : Floats.Float)
  /-- exactly `Vsingle f` -/
  | FS (f : Floats.Float32)
  /-- any number, or `Vundef` -/
  | Num (p : Aptr)
  /-- a pointer from `p`, or `Vundef` -/
  | Ptr (p : Aptr)
  /-- a pointer from `p`, or a number, or `Vundef` -/
  | Ifptr (p : Aptr)
  deriving DecidableEq, Repr

instance : Inhabited Aval := ⟨.Vbot⟩

/-- `ValueDomain.Vtop` -/
def Vtop : Aval := .Ifptr .Ptop

/-- `ValueDomain.is_uns`: the bits of `i` at positions `≥ n` are zero. -/
def IsUns (n : Z) (i : Integers.Int) : Prop :=
  ∀ m : Nat, (m : Z) < Integers.Int.zwordsize → (m : Z) ≥ n → Integers.Int.testbit i m = false

/-- `ValueDomain.is_sgn`: the bits of `i` at positions `≥ n - 1` are equal
    to the sign bit. -/
def IsSgn (n : Z) (i : Integers.Int) : Prop :=
  ∀ m : Nat, (m : Z) < Integers.Int.zwordsize → (m : Z) ≥ n - 1 →
    Integers.Int.testbit i m = Integers.Int.testbit i 31

section VMATCH
variable (bc : BlockClassification)

/-- `ValueDomain.vmatch` -/
inductive Vmatch : Val → Aval → Prop where
  | i (i) : Vmatch (.Vint i) (.I i)
  | iu (i) : Vmatch (.Vint i) (.IU i)
  | iu_undef (i) : Vmatch .Vundef (.IU i)
  | Uns (p i n) : 0 ≤ n → IsUns n i → Vmatch (.Vint i) (.Uns p n)
  | Uns_undef (p n) : Vmatch .Vundef (.Uns p n)
  | Sgn (p i n) : 0 < n → IsSgn n i → Vmatch (.Vint i) (.Sgn p n)
  | Sgn_undef (p n) : Vmatch .Vundef (.Sgn p n)
  | l (i) : Vmatch (.Vlong i) (.L i)
  | f (f) : Vmatch (.Vfloat f) (.F f)
  | s (f) : Vmatch (.Vsingle f) (.FS f)
  | num_undef (p) : Vmatch .Vundef (.Num p)
  | num_i (i p) : Vmatch (.Vint i) (.Num p)
  | num_l (i p) : Vmatch (.Vlong i) (.Num p)
  | num_f (f p) : Vmatch (.Vfloat f) (.Num p)
  | num_s (f p) : Vmatch (.Vsingle f) (.Num p)
  | ptr (b ofs p) : Pmatch bc b ofs p → Vmatch (.Vptr b ofs) (.Ptr p)
  | ptr_undef (p) : Vmatch .Vundef (.Ptr p)
  | ifptr_undef (p) : Vmatch .Vundef (.Ifptr p)
  | ifptr_i (i p) : Vmatch (.Vint i) (.Ifptr p)
  | ifptr_l (i p) : Vmatch (.Vlong i) (.Ifptr p)
  | ifptr_f (f p) : Vmatch (.Vfloat f) (.Ifptr p)
  | ifptr_s (f p) : Vmatch (.Vsingle f) (.Ifptr p)
  | ifptr_p (b ofs p) : Pmatch bc b ofs p → Vmatch (.Vptr b ofs) (.Ifptr p)

end VMATCH

/-- `ValueDomain.usize` -/
def usize (i : Integers.Int) : Z := Integers.Int.size i

/-- `ValueDomain.ssize` -/
def ssize (i : Integers.Int) : Z :=
  Integers.Int.size (if Integers.Int.lt i Integers.Int.zero then Integers.Int.not i else i) + 1

/-- `ValueDomain.urange` -/
def urange (a : Aval) : Z :=
  match a with
  | .I n | .IU n => usize n
  | .Uns _ n => n
  | _ => Integers.Int.zwordsize

/-- `ValueDomain.srange` -/
def srange (a : Aval) : Z :=
  match a with
  | .I n | .IU n => ssize n
  | .Uns _ n => n + 1
  | .Sgn _ n => n
  | _ => Integers.Int.zwordsize

/-- `ValueDomain.provenance` -/
def provenance (x : Aval) : Aptr :=
  match x with
  | .Ptr p | .Ifptr p => poffset p
  | .Uns p _ | .Sgn p _ | .Num p => p
  | _ => .Pbot

/-- `ValueDomain.ntop` -/
def ntop : Aval := .Num .Pbot
/-- `ValueDomain.ntop1` -/
def ntop1 (x : Aval) : Aval := .Num (provenance x)
/-- `ValueDomain.ntop2` -/
def ntop2 (x y : Aval) : Aval := .Num (plub (provenance x) (provenance y))

/-- `ValueDomain.int_provenance` -/
def intProvenance (strict : Bool) (i : Integers.Int) : Aptr :=
  if strict || Integers.Int.eq i Integers.Int.zero then .Pbot else .Nonstack

/-- `ValueDomain.long_provenance` -/
def longProvenance (strict : Bool) (i : Integers.Int64) : Aptr :=
  if strict || Integers.Int64.eq i Integers.Int64.zero then .Pbot else .Nonstack

/-- `ValueDomain.uns` -/
def uns (p : Aptr) (n : Z) : Aval :=
  if n ≤ 0 then .IU Integers.Int.zero
  else if n ≤ 1 then .Uns p 1
  else if n ≤ 7 then .Uns p 7
  else if n ≤ 8 then .Uns p 8
  else if n ≤ 15 then .Uns p 15
  else if n ≤ 16 then .Uns p 16
  else .Num p

/-- `ValueDomain.sgn` -/
def sgn (p : Aptr) (n : Z) : Aval :=
  if n ≤ 8 then .Sgn p 8 else if n ≤ 16 then .Sgn p 16 else .Num p

/-- `ValueDomain.vge` -/
inductive Vge : Aval → Aval → Prop where
  | bot (v) : Vge v .Vbot
  | i (i) : Vge (.I i) (.I i)
  | l (i) : Vge (.L i) (.L i)
  | f (f) : Vge (.F f) (.F f)
  | s (f) : Vge (.FS f) (.FS f)
  | iu (i) : Vge (.IU i) (.IU i)
  | iu_i (i) : Vge (.IU i) (.I i)
  | uns_i (p n i) : 0 ≤ n → IsUns n i → Vge (.Uns p n) (.I i)
  | uns_iu (p n i) : 0 ≤ n → IsUns n i → Vge (.Uns p n) (.IU i)
  | uns_uns (p1 n1 p2 n2) : n1 ≥ n2 → Pge p1 p2 → Vge (.Uns p1 n1) (.Uns p2 n2)
  | sgn_i (p n i) : 0 < n → IsSgn n i → Vge (.Sgn p n) (.I i)
  | sgn_iu (p n i) : 0 < n → IsSgn n i → Vge (.Sgn p n) (.IU i)
  | sgn_sgn (p1 n1 p2 n2) : n1 ≥ n2 → Pge p1 p2 → Vge (.Sgn p1 n1) (.Sgn p2 n2)
  | sgn_uns (p1 n1 p2 n2) : n1 > n2 → Pge p1 p2 → Vge (.Sgn p1 n1) (.Uns p2 n2)
  | num_i (p i) : Vge (.Num p) (.I i)
  | num_l (p i) : Vge (.Num p) (.L i)
  | num_f (p f) : Vge (.Num p) (.F f)
  | num_s (p f) : Vge (.Num p) (.FS f)
  | num_iu (p i) : Vge (.Num p) (.IU i)
  | num_uns (p q n) : Pge p q → Vge (.Num p) (.Uns q n)
  | num_sgn (p q n) : Pge p q → Vge (.Num p) (.Sgn q n)
  | num_num (p q) : Pge p q → Vge (.Num p) (.Num q)
  | p_p (p q) : Pge p q → Vge (.Ptr p) (.Ptr q)
  | ip_p (p q) : Pge p q → Vge (.Ifptr p) (.Ptr q)
  | ip_ip (p q) : Pge p q → Vge (.Ifptr p) (.Ifptr q)
  | ip_i (p i) : Vge (.Ifptr p) (.I i)
  | ip_l (p i) : Vge (.Ifptr p) (.L i)
  | ip_f (p f) : Vge (.Ifptr p) (.F f)
  | ip_s (p f) : Vge (.Ifptr p) (.FS f)
  | ip_iu (p i) : Vge (.Ifptr p) (.IU i)
  | ip_uns (p q n) : Pge p q → Vge (.Ifptr p) (.Uns q n)
  | ip_sgn (p q n) : Pge p q → Vge (.Ifptr p) (.Sgn q n)
  | ip_num (p q) : Pge p q → Vge (.Ifptr p) (.Num q)

/-- `ValueDomain.uns1`: like `uns` but never produces `IU Int.zero`. -/
def uns1 (p : Aptr) (n : Z) : Aval :=
  if n ≤ 1 then .Uns p 1
  else if n ≤ 7 then .Uns p 7
  else if n ≤ 8 then .Uns p 8
  else if n ≤ 15 then .Uns p 15
  else if n ≤ 16 then .Uns p 16
  else .Num p

/-- `ValueDomain.vlub_int` -/
def vlubInt (cstr : Integers.Int → Aval) (i1 i2 : Integers.Int) : Aval :=
  if Integers.Int.eq i1 i2 then cstr i1
  else if Integers.Int.lt i1 Integers.Int.zero || Integers.Int.lt i2 Integers.Int.zero
  then sgn .Pbot (max (ssize i1) (ssize i2))
  else uns1 .Pbot (max (usize i1) (usize i2))

section STRICT
variable (strict : Bool)

/-- Shared case of `vlub` (integer constant against `Uns`). -/
def vlubIUns (i : Integers.Int) (p : Aptr) (n : Z) : Aval :=
  if Integers.Int.lt i Integers.Int.zero then sgn p (max (ssize i) (n + 1))
  else uns1 p (max (usize i) n)

/-- `ValueDomain.vlub`: least upper bound of abstract values. -/
def vlub (v w : Aval) : Aval :=
  match v, w with
  | .Vbot, _ => w
  | _, .Vbot => v
  | .I i1, .I i2 => vlubInt .I i1 i2
  | .I i1, .IU i2 | .IU i1, .I i2 | .IU i1, .IU i2 => vlubInt .IU i1 i2
  | .I i, .Uns p n | .IU i, .Uns p n | .Uns p n, .I i | .Uns p n, .IU i => vlubIUns i p n
  | .I i, .Sgn p n | .IU i, .Sgn p n | .Sgn p n, .I i | .Sgn p n, .IU i =>
      sgn p (max (ssize i) n)
  | .I _, .Num p | .IU _, .Num p | .Num p, .I _ | .Num p, .IU _ => .Num p
  | .I i, .Ptr p | .I i, .Ifptr p | .IU i, .Ptr p | .IU i, .Ifptr p
  | .Ptr p, .I i | .Ifptr p, .I i | .Ptr p, .IU i | .Ifptr p, .IU i =>
      .Ifptr (plub p (intProvenance strict i))
  | .I _, .L _ | .I _, .F _ | .I _, .FS _ | .IU _, .L _ | .IU _, .F _ | .IU _, .FS _
  | .L _, .I _ | .F _, .I _ | .FS _, .I _ | .L _, .IU _ | .F _, .IU _ | .FS _, .IU _ => ntop
  | .Uns p1 n1, .Uns p2 n2 => .Uns (plub p1 p2) (max n1 n2)
  | .Uns p1 n1, .Sgn p2 n2 => sgn (plub p1 p2) (max (n1 + 1) n2)
  | .Sgn p1 n1, .Uns p2 n2 => sgn (plub p1 p2) (max n1 (n2 + 1))
  | .Sgn p1 n1, .Sgn p2 n2 => sgn (plub p1 p2) (max n1 n2)
  | .Uns p1 _, .Num p2 | .Sgn p1 _, .Num p2 | .Num p1, .Uns p2 _ | .Num p1, .Sgn p2 _ =>
      .Num (plub p1 p2)
  | .Uns p1 _, .Ptr p2 | .Uns p1 _, .Ifptr p2 | .Sgn p1 _, .Ptr p2 | .Sgn p1 _, .Ifptr p2
  | .Ptr p1, .Uns p2 _ | .Ifptr p1, .Uns p2 _ | .Ptr p1, .Sgn p2 _ | .Ifptr p1, .Sgn p2 _ =>
      .Ifptr (plub p1 p2)
  | .Uns p _, .L _ | .Uns p _, .F _ | .Uns p _, .FS _
  | .Sgn p _, .L _ | .Sgn p _, .F _ | .Sgn p _, .FS _
  | .L _, .Uns p _ | .F _, .Uns p _ | .FS _, .Uns p _
  | .L _, .Sgn p _ | .F _, .Sgn p _ | .FS _, .Sgn p _ => .Num p
  | .L i1, .L i2 => if Integers.Int64.eq i1 i2 then v else ntop
  | .L _, .Num p | .Num p, .L _ => .Num p
  | .L i, .Ptr p | .L i, .Ifptr p | .Ptr p, .L i | .Ifptr p, .L i =>
      .Ifptr (plub p (longProvenance strict i))
  | .L _, .F _ | .L _, .FS _ | .F _, .L _ | .FS _, .L _ => ntop
  | .F f1, .F f2 => if f1 = f2 then v else ntop
  | .F _, .Num p | .Num p, .F _ => .Num p
  | .F _, .Ptr p | .F _, .Ifptr p | .Ptr p, .F _ | .Ifptr p, .F _ => .Ifptr p
  | .F _, .FS _ | .FS _, .F _ => ntop
  | .FS f1, .FS f2 => if f1 = f2 then v else ntop
  | .FS _, .Num p | .Num p, .FS _ => .Num p
  | .FS _, .Ptr p | .FS _, .Ifptr p | .Ptr p, .FS _ | .Ifptr p, .FS _ => .Ifptr p
  | .Num p1, .Num p2 => .Num (plub p1 p2)
  | .Num p1, .Ptr p2 | .Num p1, .Ifptr p2 | .Ifptr p1, .Num p2 | .Ptr p1, .Num p2 =>
      .Ifptr (plub p1 p2)
  | .Ptr p1, .Ptr p2 => .Ptr (plub p1 p2)
  | .Ptr p1, .Ifptr p2 | .Ifptr p1, .Ptr p2 | .Ifptr p1, .Ifptr p2 => .Ifptr (plub p1 p2)

/-- `ValueDomain.aptr_of_aval` -/
def aptrOfAval (v : Aval) : Aptr :=
  match v with
  | .Ptr p | .Ifptr p => p
  | .Num p | .Uns p _ | .Sgn p _ => if strict then .Pbot else p
  | .I i => intProvenance strict i
  | .L i => longProvenance strict i
  | _ => .Pbot

end STRICT

/-- `ValueDomain.vplub` -/
def vplub (v : Aval) (p : Aptr) : Aptr :=
  match v with
  | .Ptr q | .Ifptr q => plub q p
  | _ => p

/-- `ValueDomain.vpincl` -/
def vpincl (v : Aval) (p : Aptr) : Bool :=
  match v with
  | .Ptr q | .Ifptr q | .Num q | .Uns q _ | .Sgn q _ => pincl q p
  | _ => true

/-- `ValueDomain.vincl` -/
def vincl (v w : Aval) : Bool :=
  match v, w with
  | .Vbot, _ => true
  | .I i, .I j => decide (i = j)
  | .I i, .IU j => decide (i = j)
  | .IU i, .IU j => decide (i = j)
  | .I i, .Uns _ n | .IU i, .Uns _ n =>
      decide (Integers.Int.zero_ext n.toNat i = i) && decide (0 ≤ n)
  | .I i, .Sgn _ n | .IU i, .Sgn _ n =>
      decide (Integers.Int.sign_ext n.toNat i = i) && decide (0 < n)
  | .Uns p n, .Uns q m => decide (n ≤ m) && pincl p q
  | .Uns p n, .Sgn q m => decide (n < m) && pincl p q
  | .Sgn p n, .Sgn q m => decide (n ≤ m) && pincl p q
  | .L i, .L j => decide (i = j)
  | .F i, .F j => decide (i = j)
  | .FS i, .FS j => decide (i = j)
  | .I _, .Num _ | .IU _, .Num _ | .L _, .Num _ | .F _, .Num _ | .FS _, .Num _
  | .I _, .Ifptr _ | .IU _, .Ifptr _ | .L _, .Ifptr _ | .F _, .Ifptr _ | .FS _, .Ifptr _ => true
  | .Uns p _, .Num q | .Sgn p _, .Num q | .Num p, .Num q => pincl p q
  | .Ptr p, .Ptr q => pincl p q
  | .Ptr p, .Ifptr q | .Ifptr p, .Ifptr q | .Num p, .Ifptr q | .Uns p _, .Ifptr q
  | .Sgn p _, .Ifptr q => pincl p q
  | _, _ => false

/-- `ValueDomain.genv_match` -/
def GenvMatch {F V : Type} (bc : BlockClassification) (ge : Genv F V) : Prop :=
  (∀ id b, Genv.findSymbol ge id = some b ↔ bc b = .BCglob id) ∧
  (∀ b, b < ge.genv_next → bc b ≠ .BCinvalid ∧ bc b ≠ .BCstack)

end ValueDomain
end CC
