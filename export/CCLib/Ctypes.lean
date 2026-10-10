/-
  C types, their layout, and composite environments — port of the semantic core
  of `cfrontend/Ctypes.v` (lines 1–1208 plus the `PROGRAMS` section; the
  `STABILITY` section and the ~440 lines of linking machinery are pass-proof
  support and are skipped, which also removes any need for `common/Linking.v`).

  The *syntax* here (`Ty`, `Attr`, `Member`, `CompositeDef`, the `tint`/`tptr`
  short names …) previously lived in `Clightdefs.lean`; it moved so that `Cop`
  and the semantics can use it.  All names are unchanged, so files emitted by
  `clightgen -lean` are unaffected.

  ## One documented deviation: `Composite` carries no proofs

  CompCert's `composite` record has three `Prop` fields — `co_sizeof_pos`,
  `co_alignof_two_p` (an existential!), `co_sizeof_alignof` — discharged by
  `Program Definition composite_of_def` (3 obligations).  They are consumed by
  the *compiler* proofs (`Cshmgenproof`), never by the Clight step relation, so
  we keep only the data.  That makes `compositeOfDef` and `buildCompositeEnv`
  plain total computations.

  Coq's `Z.div` rounds toward −∞ while Lean's `Int./` truncates toward zero, so
  `align`/`floor`/`bytesOfBits` use `Int.fdiv` to match exactly.
-/
import CCLib.AST
import CCLib.Maps

namespace CC

/-! ## Error monad (`common/Errors.v`, simplified)

CompCert's `errmsg` is a list of message items carrying idents; we use a plain
`String`, which is enough since nothing in the semantics inspects it. -/

inductive Res (A : Type) where
  | OK (a : A)
  | Error (msg : String)
  deriving DecidableEq, Inhabited

namespace Res
def isOK {A : Type} : Res A → Bool
  | .OK _ => true
  | .Error _ => false

def toOption {A : Type} : Res A → Option A
  | .OK a => some a
  | .Error _ => none

def bind {A B : Type} : Res A → (A → Res B) → Res B
  | .OK a, f => f a
  | .Error m, _ => .Error m

instance : Monad Res where
  pure := .OK
  bind := bind
end Res

/-! ## Alignment arithmetic (`lib/Coqlib.v`) -/

/-- Coq's `Z.div`: floor division (Lean's `/` on `Int` truncates instead). -/
def zdiv (a b : Z) : Z := Int.fdiv a b

/-- `Coqlib.align` — round `n` up to a multiple of `amount`. -/
def align (n amount : Z) : Z := zdiv (n + amount - 1) amount * amount
/-- `Coqlib.floor` — round `n` down to a multiple of `amount`. -/
def floorZ (n amount : Z) : Z := zdiv n amount * amount
/-- `Ctypes.bytes_of_bits` -/
def bytesOfBits (n : Z) : Z := zdiv (n + 7) 8

/-! ## Type syntax -/

/-- `Ctypes.signedness` -/
inductive Signedness where
  | Signed | Unsigned
  deriving DecidableEq, Repr, Inhabited

/-- `Ctypes.intsize` -/
inductive IntSize where
  | I8 | I16 | I32 | IBool
  deriving DecidableEq, Repr, Inhabited

/-- `Ctypes.floatsize` -/
inductive FloatSize where
  | F32 | F64
  deriving DecidableEq, Repr, Inhabited

/-- `Ctypes.attr` -/
structure Attr where
  attr_volatile : Bool
  /-- log2 of the required alignment (`_Alignas`) -/
  attr_alignas : Option Nat
  deriving DecidableEq, Repr, Inhabited

def noattr : Attr := { attr_volatile := false, attr_alignas := none }

/-- `Ctypes.type` -/
inductive Ty where
  | Tvoid
  | Tint (sz : IntSize) (sg : Signedness) (a : Attr)
  | Tlong (sg : Signedness) (a : Attr)
  | Tfloat (sz : FloatSize) (a : Attr)
  | Tpointer (t : Ty) (a : Attr)
  | Tarray (t : Ty) (sz : Z) (a : Attr)
  | Tfunction (targs : List Ty) (tres : Ty) (cc : CallConv)
  | Tstruct (id : Ident) (a : Attr)
  | Tunion (id : Ident) (a : Attr)

-- No `deriving DecidableEq, Repr`: `Tfunction` recurses through `List Ty`, which
-- Lean's deriving handlers do not traverse.  Nothing in the semantics compares
-- types structurally (CompCert's `type_eq` is used only by the linking code we
-- skip), so this costs nothing.
instance : Inhabited Ty := ⟨Ty.Tvoid⟩

/-! ### Decidable equality for `Ty`

Lean's deriving handlers cannot traverse `Tfunction`'s `List Ty`, so this is the
hand-written equivalent of CompCert's `Ctypes.type_eq`.  The interpreter needs it:
`eval_lvalue`'s `Evar_local` rule requires the type recorded in the local
environment to *equal* the expression's type annotation.

The proofs are written in equation style with deliberately incomplete patterns —
Lean discharges the mismatched-constructor cases itself, since `tyBeq` is `false`
there. -/

mutual
def tyBeq : Ty → Ty → Bool
  | .Tvoid, .Tvoid => true
  | .Tint s1 g1 a1, .Tint s2 g2 a2 => s1 == s2 && g1 == g2 && a1 == a2
  | .Tlong g1 a1, .Tlong g2 a2 => g1 == g2 && a1 == a2
  | .Tfloat s1 a1, .Tfloat s2 a2 => s1 == s2 && a1 == a2
  | .Tpointer t1 a1, .Tpointer t2 a2 => tyBeq t1 t2 && a1 == a2
  | .Tarray t1 n1 a1, .Tarray t2 n2 a2 => tyBeq t1 t2 && n1 == n2 && a1 == a2
  | .Tfunction as1 r1 c1, .Tfunction as2 r2 c2 =>
      tyBeqL as1 as2 && tyBeq r1 r2 && c1 == c2
  | .Tstruct i1 a1, .Tstruct i2 a2 => i1 == i2 && a1 == a2
  | .Tunion i1 a1, .Tunion i2 a2 => i1 == i2 && a1 == a2
  | _, _ => false

def tyBeqL : List Ty → List Ty → Bool
  | [], [] => true
  | x :: xs, y :: ys => tyBeq x y && tyBeqL xs ys
  | _, _ => false
end

mutual
theorem tyBeq_eq : ∀ (a b : Ty), tyBeq a b = true → a = b
  | .Tvoid, .Tvoid, _ => rfl
  | .Tint _ _ _, .Tint _ _ _, h => by simp_all [tyBeq]
  | .Tlong _ _, .Tlong _ _, h => by simp_all [tyBeq]
  | .Tfloat _ _, .Tfloat _ _, h => by simp_all [tyBeq]
  | .Tpointer t1 _, .Tpointer t2 _, h => by
      rw [tyBeq, Bool.and_eq_true] at h
      rw [tyBeq_eq t1 t2 h.1, of_decide_eq_true h.2]
  | .Tarray t1 _ _, .Tarray t2 _ _, h => by
      rw [tyBeq, Bool.and_eq_true, Bool.and_eq_true] at h
      rw [tyBeq_eq t1 t2 h.1.1, of_decide_eq_true h.1.2, of_decide_eq_true h.2]
  | .Tfunction as1 r1 _, .Tfunction as2 r2 _, h => by
      rw [tyBeq, Bool.and_eq_true, Bool.and_eq_true] at h
      rw [tyBeqL_eq as1 as2 h.1.1, tyBeq_eq r1 r2 h.1.2, of_decide_eq_true h.2]
  | .Tstruct _ _, .Tstruct _ _, h => by simp_all [tyBeq]
  | .Tunion _ _, .Tunion _ _, h => by simp_all [tyBeq]

theorem tyBeqL_eq : ∀ (as bs : List Ty), tyBeqL as bs = true → as = bs
  | [], [], _ => rfl
  | x :: xs, y :: ys, h => by
      rw [tyBeqL, Bool.and_eq_true] at h
      rw [tyBeq_eq x y h.1, tyBeqL_eq xs ys h.2]
end

mutual
theorem tyBeq_refl : ∀ (a : Ty), tyBeq a a = true
  | .Tvoid => rfl
  | .Tint _ _ _ => by simp [tyBeq]
  | .Tlong _ _ => by simp [tyBeq]
  | .Tfloat _ _ => by simp [tyBeq]
  | .Tpointer t _ => by simp [tyBeq, tyBeq_refl t]
  | .Tarray t _ _ => by simp [tyBeq, tyBeq_refl t]
  | .Tfunction as r _ => by simp [tyBeq, tyBeqL_refl as, tyBeq_refl r]
  | .Tstruct _ _ => by simp [tyBeq]
  | .Tunion _ _ => by simp [tyBeq]

theorem tyBeqL_refl : ∀ (as : List Ty), tyBeqL as as = true
  | [] => rfl
  | x :: xs => by simp [tyBeqL, tyBeq_refl x, tyBeqL_refl xs]
end

instance : DecidableEq Ty := fun a b =>
  if h : tyBeq a b = true then isTrue (tyBeq_eq a b h)
  else isFalse (fun heq => h (heq ▸ tyBeq_refl a))

/-- `Ctypes.bitsize_intsize` -/
def bitsizeIntsize : IntSize → Z
  | .I8 => 8 | .I16 => 16 | .I32 => 32 | .IBool => 1

/-! ### Short names for types (mirror of `export/Ctypesdefs.v`) -/

def tvoid   : Ty := Ty.Tvoid
def tschar  : Ty := Ty.Tint IntSize.I8 Signedness.Signed noattr
def tuchar  : Ty := Ty.Tint IntSize.I8 Signedness.Unsigned noattr
def tshort  : Ty := Ty.Tint IntSize.I16 Signedness.Signed noattr
def tushort : Ty := Ty.Tint IntSize.I16 Signedness.Unsigned noattr
def tint    : Ty := Ty.Tint IntSize.I32 Signedness.Signed noattr
def tuint   : Ty := Ty.Tint IntSize.I32 Signedness.Unsigned noattr
def tbool   : Ty := Ty.Tint IntSize.IBool Signedness.Unsigned noattr
def tlong   : Ty := Ty.Tlong Signedness.Signed noattr
def tulong  : Ty := Ty.Tlong Signedness.Unsigned noattr
def tfloat  : Ty := Ty.Tfloat FloatSize.F32 noattr
def tdouble : Ty := Ty.Tfloat FloatSize.F64 noattr
def tptr (t : Ty) : Ty := Ty.Tpointer t noattr
def tarray (t : Ty) (sz : Z) : Ty := Ty.Tarray t sz noattr

/-- `Ctypes.attr_of_type` -/
def Ty.attr : Ty → Attr
  | .Tvoid => noattr
  | .Tint _ _ a => a
  | .Tlong _ a => a
  | .Tfloat _ a => a
  | .Tpointer _ a => a
  | .Tarray _ _ a => a
  | .Tfunction _ _ _ => noattr
  | .Tstruct _ a => a
  | .Tunion _ a => a

/-- `Ctypesdefs.tattr` — replace the top-level attributes. -/
def tattr (a : Attr) (ty : Ty) : Ty :=
  match ty with
  | .Tvoid => .Tvoid
  | .Tint sz si _ => .Tint sz si a
  | .Tlong si _ => .Tlong si a
  | .Tfloat sz _ => .Tfloat sz a
  | .Tpointer elt _ => .Tpointer elt a
  | .Tarray elt sz _ => .Tarray elt sz a
  | .Tfunction args res cc => .Tfunction args res cc
  | .Tstruct id _ => .Tstruct id a
  | .Tunion id _ => .Tunion id a

/-- `Ctypes.remove_attributes` -/
def removeAttributes (ty : Ty) : Ty := tattr noattr ty

def volatile_attr : Attr := { attr_volatile := true, attr_alignas := none }
def tvolatile (ty : Ty) : Ty := tattr volatile_attr ty
def talignas (n : Nat) (ty : Ty) : Ty :=
  tattr { attr_volatile := false, attr_alignas := some n } ty
def tvolatile_alignas (n : Nat) (ty : Ty) : Ty :=
  tattr { attr_volatile := true, attr_alignas := some n } ty

/-- `Ctypes.typeconv` — the usual C conversions (integer promotion, array and
    function decay).  Used by every `classify_*` in `Cop`. -/
def typeconv : Ty → Ty
  | .Tint .I8 _ _ | .Tint .I16 _ _ | .Tint .IBool _ _ => tint
  | .Tarray t _ _ => .Tpointer t noattr
  | ty@(.Tfunction _ _ _) => .Tpointer ty noattr
  | ty => removeAttributes ty

/-! ## Composites -/

/-- `Ctypes.struct_or_union` -/
inductive SU where
  | Struct | Union
  deriving DecidableEq, Repr, Inhabited

/-- `Ctypes.member` -/
inductive Member where
  | Member_plain (id : Ident) (t : Ty)
  | Member_bitfield (id : Ident) (sz : IntSize) (sg : Signedness) (a : Attr)
                    (width : Z) (padding : Bool)
  -- `DecidableEq` (not derivable for `Ty` itself, but usable here) is needed to
  -- state concrete `composite_env` facts; see `examples/StructSep.lean`.
  deriving DecidableEq

instance : Inhabited Member := ⟨Member.Member_plain Positive.xH Ty.Tvoid⟩

/-- `Ctypes.name_member` -/
def Member.name : Member → Ident
  | .Member_plain id _ => id
  | .Member_bitfield id _ _ _ _ _ => id

/-- `Ctypes.type_member`.  Note the sign twist: an unsigned bitfield narrower
    than its carrier reads back through a *signed* type. -/
def Member.type : Member → Ty
  | .Member_plain _ t => t
  | .Member_bitfield _ sz sg a w _ =>
      let sg' := if w < bitsizeIntsize sz then Signedness.Signed else sg
      .Tint sz sg' a

/-- `Ctypes.member_is_padding` -/
def Member.isPadding : Member → Bool
  | .Member_plain _ _ => false
  | .Member_bitfield _ _ _ _ _ p => p

/-- `Ctypes.composite_definition` -/
inductive CompositeDef where
  | Composite (id : Ident) (su : SU) (m : List Member) (a : Attr)

instance : Inhabited CompositeDef :=
  ⟨CompositeDef.Composite Positive.xH SU.Struct [] noattr⟩

def CompositeDef.name : CompositeDef → Ident
  | .Composite id _ _ _ => id

/-- `Ctypes.composite`, minus the three `Prop` fields (see the header note). -/
structure Composite where
  co_su : SU
  co_members : List Member
  co_attr : Attr
  co_sizeof : Z
  co_alignof : Z
  co_rank : Nat
  deriving DecidableEq

instance : Inhabited Composite :=
  ⟨{ co_su := SU.Struct, co_members := [], co_attr := noattr,
     co_sizeof := 0, co_alignof := 1, co_rank := 0 }⟩

/-- `Ctypes.composite_env` -/
abbrev CompositeEnv := PTree Composite

/-- `Ctypes.bitfield` — how a member sits inside its carrier. -/
inductive Bitfield where
  | Full
  | Bits (sz : IntSize) (sg : Signedness) (pos : Z) (width : Z)
  deriving DecidableEq, Repr, Inhabited

/-! ## Sizes and alignments -/

/-- `Ctypes.align_attr` — an explicit `_Alignas(2^l)` overrides the natural
    alignment. -/
def alignAttr (a : Attr) (al : Z) : Z :=
  match a.attr_alignas with
  | some l => (2 : Z) ^ l
  | none => al

/-- `Ctypes.alignof` -/
def alignof (env : CompositeEnv) : Ty → Z
  | ty@(.Tvoid) => alignAttr ty.attr 1
  | ty@(.Tint .I8 _ _) => alignAttr ty.attr 1
  | ty@(.Tint .I16 _ _) => alignAttr ty.attr 2
  | ty@(.Tint .I32 _ _) => alignAttr ty.attr 4
  | ty@(.Tint .IBool _ _) => alignAttr ty.attr 1
  | ty@(.Tlong _ _) => alignAttr ty.attr (Archi.align_int64 : Z)
  | ty@(.Tfloat .F32 _) => alignAttr ty.attr 4
  | ty@(.Tfloat .F64 _) => alignAttr ty.attr (Archi.align_float64 : Z)
  | ty@(.Tpointer _ _) => alignAttr ty.attr (if Archi.ptr64 then 8 else 4)
  | ty@(.Tarray t' _ _) => alignAttr ty.attr (alignof env t')
  | ty@(.Tfunction _ _ _) => alignAttr ty.attr 1
  | ty@(.Tstruct id _) =>
      alignAttr ty.attr (match env.get id with | some co => co.co_alignof | none => 1)
  | ty@(.Tunion id _) =>
      alignAttr ty.attr (match env.get id with | some co => co.co_alignof | none => 1)

/-- `Ctypes.sizeof` -/
def sizeof (env : CompositeEnv) : Ty → Z
  | .Tvoid => 1
  | .Tint .I8 _ _ => 1
  | .Tint .I16 _ _ => 2
  | .Tint .I32 _ _ => 4
  | .Tint .IBool _ _ => 1
  | .Tlong _ _ => 8
  | .Tfloat .F32 _ => 4
  | .Tfloat .F64 _ => 8
  | .Tpointer _ _ => if Archi.ptr64 then 8 else 4
  | .Tarray t' n _ => sizeof env t' * max 0 n
  | .Tfunction _ _ _ => 1
  | .Tstruct id _ => match env.get id with | some co => co.co_sizeof | none => 0
  | .Tunion id _ => match env.get id with | some co => co.co_sizeof | none => 0

/-- `Ctypes.complete_type` -/
def completeType (env : CompositeEnv) : Ty → Bool
  | .Tvoid => false
  | .Tint _ _ _ => true
  | .Tlong _ _ => true
  | .Tfloat _ _ => true
  | .Tpointer _ _ => true
  | .Tarray t' _ _ => completeType env t'
  | .Tfunction _ _ _ => false
  | .Tstruct id _ => (env.get id).isSome
  | .Tunion id _ => (env.get id).isSome

/-! ## Field layout (the `LAYOUT` section) -/

def bitalignof (env : CompositeEnv) (t : Ty) : Z := alignof env t * 8
def bitsizeof (env : CompositeEnv) (t : Ty) : Z := sizeof env t * 8

/-- `Ctypes.bitalignof_intsize` -/
def bitalignofIntsize : IntSize → Z
  | .I8 | .IBool => 8
  | .I16 => 16
  | .I32 => 32

/-- `Ctypes.next_field` — bit position after laying out `m` at `pos`. -/
def nextField (env : CompositeEnv) (pos : Z) : Member → Z
  | .Member_plain _ t => align pos (bitalignof env t) + bitsizeof env t
  | .Member_bitfield _ sz _ _ w _ =>
      let s := bitalignofIntsize sz
      if w ≤ 0 then align pos s
      else
        let curr := floorZ pos s
        let next := curr + s
        if pos + w ≤ next then pos + w else next + w

/-- `Ctypes.layout_field` — byte offset and bitfield designation of `m`. -/
def layoutField (env : CompositeEnv) (pos : Z) : Member → Res (Z × Bitfield)
  | .Member_plain _ t => .OK (zdiv (align pos (bitalignof env t)) 8, .Full)
  | .Member_bitfield _ sz sg _ w _ =>
      if w ≤ 0 then .Error "accessing zero-width bitfield"
      else if bitsizeIntsize sz < w then .Error "bitfield too wide"
      else
        let s := bitalignofIntsize sz
        let start := floorZ pos s
        let next := start + s
        if pos + w ≤ next then .OK (zdiv start 8, .Bits sz sg (pos - start) w)
        else .OK (zdiv next 8, .Bits sz sg 0 w)

/-- `Ctypes.layout_start` -/
def layoutStart (p : Z) : Bitfield → Z
  | .Full => p * 8
  | .Bits _ _ pos _ => p * 8 + pos

/-- `Ctypes.layout_width` -/
def layoutWidth (env : CompositeEnv) (t : Ty) : Bitfield → Z
  | .Full => bitsizeof env t
  | .Bits _ _ _ w => w

/-! ## Composite sizes -/

/-- `Ctypes.alignof_composite` -/
def alignofComposite (env : CompositeEnv) : List Member → Z
  | [] => 1
  | m :: ms =>
      if m.isPadding then alignofComposite env ms
      else max (alignof env m.type) (alignofComposite env ms)

/-- `Ctypes.bitsizeof_struct` -/
def bitsizeofStruct (env : CompositeEnv) (cur : Z) : List Member → Z
  | [] => cur
  | m :: ms => bitsizeofStruct env (nextField env cur m) ms

/-- `Ctypes.sizeof_struct` -/
def sizeofStruct (env : CompositeEnv) (m : List Member) : Z :=
  bytesOfBits (bitsizeofStruct env 0 m)

/-- `Ctypes.sizeof_union` -/
def sizeofUnion (env : CompositeEnv) : List Member → Z
  | [] => 0
  | m :: ms => max (sizeof env m.type) (sizeofUnion env ms)

/-- `Ctypes.sizeof_composite` -/
def sizeofComposite (env : CompositeEnv) : SU → List Member → Z
  | .Struct, m => sizeofStruct env m
  | .Union, m => sizeofUnion env m

/-- `Ctypes.field_type` -/
def fieldType (id : Ident) : List Member → Res Ty
  | [] => .Error "Unknown field"
  | m :: ms => if id = m.name then .OK m.type else fieldType id ms

/-- `Ctypes.field_offset_rec` -/
def fieldOffsetRec (env : CompositeEnv) (id : Ident) (pos : Z) :
    List Member → Res (Z × Bitfield)
  | [] => .Error "Unknown field"
  | m :: ms =>
      if id = m.name then layoutField env pos m
      else fieldOffsetRec env id (nextField env pos m) ms

/-- `Ctypes.field_offset` — byte offset of a struct field. -/
def fieldOffset (env : CompositeEnv) (id : Ident) (ms : List Member) :
    Res (Z × Bitfield) := fieldOffsetRec env id 0 ms

/-- `Ctypes.union_field_offset` — every union member starts at bit 0. -/
def unionFieldOffset (env : CompositeEnv) (id : Ident) :
    List Member → Res (Z × Bitfield)
  | [] => .Error "Unknown field"
  | m :: ms =>
      if id = m.name then layoutField env 0 m else unionFieldOffset env id ms

/-! ## Access modes -/

/-- `Ctypes.mode` — how a datum of a given type is accessed. -/
inductive AccessMode where
  | By_value (chunk : Chunk)
  | By_reference
  | By_copy
  | By_nothing
  deriving DecidableEq, Repr, Inhabited

/-- `Ctypes.access_mode` -/
def accessMode : Ty → AccessMode
  | .Tint .I8 .Signed _ => .By_value .Mint8signed
  | .Tint .I8 .Unsigned _ => .By_value .Mint8unsigned
  | .Tint .I16 .Signed _ => .By_value .Mint16signed
  | .Tint .I16 .Unsigned _ => .By_value .Mint16unsigned
  | .Tint .I32 _ _ => .By_value .Mint32
  | .Tint .IBool _ _ => .By_value .Mbool
  | .Tlong _ _ => .By_value .Mint64
  | .Tfloat .F32 _ => .By_value .Mfloat32
  | .Tfloat .F64 _ => .By_value .Mfloat64
  | .Tvoid => .By_nothing
  | .Tpointer _ _ => .By_value Mptr
  | .Tarray _ _ _ => .By_reference
  | .Tfunction _ _ _ => .By_reference
  | .Tstruct _ _ => .By_copy
  | .Tunion _ _ => .By_copy

/-- `Ctypes.type_is_volatile` -/
def typeIsVolatile (ty : Ty) : Bool :=
  match accessMode ty with
  | .By_value _ => ty.attr.attr_volatile
  | _ => false

/-- `Ctypes.alignof_blockcopy` — the alignment a `By_copy` assignment must
    respect.  Capped at 8 for composites. -/
def alignofBlockcopy (env : CompositeEnv) : Ty → Z
  | .Tvoid => 1
  | .Tint .I8 _ _ => 1
  | .Tint .I16 _ _ => 2
  | .Tint .I32 _ _ => 4
  | .Tint .IBool _ _ => 1
  | .Tlong _ _ => Archi.align_int64
  | .Tfloat .F32 _ => 4
  | .Tfloat .F64 _ => Archi.align_float64
  | .Tpointer _ _ => if Archi.ptr64 then 8 else 4
  | .Tarray t' _ _ => alignofBlockcopy env t'
  | .Tfunction _ _ _ => 1
  | .Tstruct id _ =>
      match env.get id with | some co => min 8 co.co_alignof | none => 1
  | .Tunion id _ =>
      match env.get id with | some co => min 8 co.co_alignof | none => 1

/-! ## Ranks, and building the composite environment -/

/-- `Ctypes.rank_type` -/
def rankType (ce : CompositeEnv) : Ty → Nat
  | .Tarray t' _ _ => rankType ce t' + 1
  | .Tstruct id _ => match ce.get id with | none => 0 | some co => co.co_rank + 1
  | .Tunion id _ => match ce.get id with | none => 0 | some co => co.co_rank + 1
  | _ => 0

/-- `Ctypes.rank_members` -/
def rankMembers (ce : CompositeEnv) : List Member → Nat
  | [] => 0
  | .Member_plain _ t :: m => max (rankType ce t) (rankMembers ce m)
  | .Member_bitfield _ _ _ _ _ _ :: m => rankMembers ce m

/-- `Ctypes.complete_members` -/
def completeMembers (env : CompositeEnv) : List Member → Bool
  | [] => true
  | m :: ms => completeType env m.type && completeMembers env ms

/-- `Ctypes.composite_of_def` -/
def compositeOfDef (env : CompositeEnv) (id : Ident) (su : SU)
    (m : List Member) (a : Attr) : Res Composite :=
  if (env.get id).isSome then
    .Error "Multiple definitions of struct or union"
  else if !completeMembers env m then
    .Error "Incomplete struct or union"
  else
    let al := alignAttr a (alignofComposite env m)
    .OK { co_su := su, co_members := m, co_attr := a,
          co_sizeof := align (sizeofComposite env su m) al,
          co_alignof := al,
          co_rank := rankMembers env m }

/-- `Ctypes.add_composite_definitions` -/
def addCompositeDefinitions (env : CompositeEnv) :
    List CompositeDef → Res CompositeEnv
  | [] => .OK env
  | .Composite id su m a :: defs =>
      match compositeOfDef env id su m a with
      | .OK co => addCompositeDefinitions (env.set id co) defs
      | .Error e => .Error e

/-- `Ctypes.build_composite_env` -/
def buildCompositeEnv (defs : List CompositeDef) : Res CompositeEnv :=
  addCompositeDefinitions PTree.empty defs

/-! ## Type signatures (`Ctypes` → `AST`) -/

/-- `Ctypes.typ_of_type` -/
def typOfType : Ty → ATyp
  | .Tvoid => .Tint
  | .Tint _ _ _ => .Tint
  | .Tlong _ _ => .Tlong
  | .Tfloat .F32 _ => .Tsingle
  | .Tfloat .F64 _ => .Tfloat
  | .Tpointer _ _ | .Tarray _ _ _ | .Tfunction _ _ _
  | .Tstruct _ _ | .Tunion _ _ => Tptr

/-- `Ctypes.argtype_of_type` -/
def argtypeOfType : Ty → XType
  | .Tvoid => .Xvoid
  | .Tint .IBool _ _ => .Xbool
  | .Tint .I8 .Signed _ => .Xint8signed
  | .Tint .I8 .Unsigned _ => .Xint8unsigned
  | .Tint .I16 .Signed _ => .Xint16signed
  | .Tint .I16 .Unsigned _ => .Xint16unsigned
  | .Tint .I32 _ _ => .Xint
  | .Tlong _ _ => .Xlong
  | .Tfloat .F32 _ => .Xsingle
  | .Tfloat .F64 _ => .Xfloat
  | .Tpointer _ _ | .Tarray _ _ _ | .Tfunction _ _ _
  | .Tstruct _ _ | .Tunion _ _ => .Xptr

/-- `Ctypes.rettype_of_type` -/
def rettypeOfType : Ty → XType
  | .Tvoid => .Xvoid
  | ty => argtypeOfType ty

/-- `Ctypes.signature_of_type` -/
def signatureOfType (args : List Ty) (res : Ty) (cc : CallConv) : Signature :=
  mksignature (args.map argtypeOfType) (rettypeOfType res) cc

/-! ## Function definitions and programs -/

/-- `Ctypes.fundef` -/
inductive FunDefGen (F : Type) where
  | Internal (f : F)
  | External (ef : ExtFun) (targs : List Ty) (tres : Ty) (cc : CallConv)

end CC
