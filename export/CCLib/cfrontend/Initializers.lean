/-
  Compile-time evaluation of initializers for global C variables — port of
  `cfrontend/Initializers.v`.

  * `constval`: evaluation of constant expressions, with the same `Val` type
    and `sem_*` functions as the CompCert C semantics, but with pointers
    interpreted symbolically (`Vptr id ofs` is the address of global `id`
    plus `ofs`; in the port, as in CompCert, identifiers and blocks are both
    positive numbers);
  * the abstract initialization `State` with `store_data`, `store_int`,
    `load_int` and their helpers (`normalize`, `decompose`, `trisection`,
    `pad_to`);
  * `Initializer`/`InitializerList` and the translation `transl_init`.

  Differences from Rocq:
  * error messages are plain strings (the port's `Res`), so `MSG … :: CTX id`
    messages lose the identifier;
  * `Z.iter n` (used by `add_zeros`) is `List.replicate n.toNat`;
  * the nested `fix init` of `transl_init_struct` is split: the search for the
    next initialized member is the separate function `skipUninitialized`, so
    that the translation stays structurally recursive on initializers.
-/
import CCLib.cfrontend.Csyntax
import CCLib.common.Memdata

namespace CC
namespace Initializers

open Csyntax

/-- `assertion` of the error monad. -/
@[inline] def assertion {A : Type} (b : Bool) (k : Res A) : Res A :=
  if b then k else .Error "Assertion failed"

/-! ## Evaluation of compile-time constant expressions -/

/-- `Initializers.do_cast` -/
def doCast (v : Val) (t1 t2 : Ty) : Res Val :=
  match Cop.semCast v t1 t2 Mem.empty with
  | some v' => .OK v'
  | none => .Error "undefined cast"

/-- `Initializers.lookup_composite` -/
def lookupComposite (ce : CompositeEnv) (id : Ident) : Res Composite :=
  match ce.get id with
  | some co => .OK co
  | none => .Error "Undefined struct or union"

/-- `Initializers.constval`: the value of the constant expression `a`
    (`Vptr id ofs` stands for the address of global variable `id` plus `ofs`). -/
def constval (ce : CompositeEnv) : Csyntax.Expr → Res Val
  | .Eval v _ =>
      match v with
      | .Vint _ | .Vfloat _ | .Vsingle _ | .Vlong _ => .OK v
      | .Vptr _ _ | .Vundef => .Error "illegal constant"
  | .Evalof l ty =>
      match accessMode ty with
      | .By_reference | .By_copy => constval ce l
      | _ => .Error "dereferencing of an l-value"
  | .Eaddrof l _ => constval ce l
  | .Eunop op r1 _ => do
      let v1 ← constval ce r1
      match Cop.semUnaryOperation op v1 (Csyntax.typeof r1) Mem.empty with
      | some v => .OK v
      | none => .Error "undefined unary operation"
  | .Ebinop op r1 r2 _ => do
      let v1 ← constval ce r1
      let v2 ← constval ce r2
      match Cop.semBinaryOperation ce op v1 (Csyntax.typeof r1) v2 (Csyntax.typeof r2) Mem.empty with
      | some v => .OK v
      | none => .Error "undefined binary operation"
  | .Ecast r ty => do
      let v1 ← constval ce r
      doCast v1 (Csyntax.typeof r) ty
  | .Esizeof ty1 _ => .OK (Val.Vptrofs (Integers.Ptrofs.repr (sizeof ce ty1)))
  | .Ealignof ty1 _ => .OK (Val.Vptrofs (Integers.Ptrofs.repr (alignof ce ty1)))
  | .Eseqand r1 r2 _ => do
      let v1 ← constval ce r1
      let v2 ← constval ce r2
      match Cop.boolVal v1 (Csyntax.typeof r1) Mem.empty with
      | some true => doCast v2 (Csyntax.typeof r2) type_bool
      | some false => .OK (.Vint Integers.Int.zero)
      | none => .Error "undefined && operation"
  | .Eseqor r1 r2 _ => do
      let v1 ← constval ce r1
      let v2 ← constval ce r2
      match Cop.boolVal v1 (Csyntax.typeof r1) Mem.empty with
      | some false => doCast v2 (Csyntax.typeof r2) type_bool
      | some true => .OK (.Vint Integers.Int.one)
      | none => .Error "undefined || operation"
  | .Econdition r1 r2 r3 ty => do
      let v1 ← constval ce r1
      let v2 ← constval ce r2
      let v3 ← constval ce r3
      match Cop.boolVal v1 (Csyntax.typeof r1) Mem.empty with
      | some true => doCast v2 (Csyntax.typeof r2) ty
      | some false => doCast v3 (Csyntax.typeof r3) ty
      | none => .Error "condition is undefined"
  | .Ecomma r1 r2 _ => do
      let _ ← constval ce r1
      constval ce r2
  | .Evar x _ => .OK (.Vptr x Integers.Ptrofs.zero)
  | .Ederef r _ => constval ce r
  | .Efield l f _ => do
      let (delta, bf) ←
        match Csyntax.typeof l with
        | .Tstruct id _ => do
            let co ← lookupComposite ce id
            fieldOffset ce f co.co_members
        | .Tunion id _ => do
            let co ← lookupComposite ce id
            unionFieldOffset ce f co.co_members
        | _ => .Error "ill-typed field access"
      let v ← constval ce l
      match bf with
      | .Full =>
          .OK (if Archi.ptr64 then Val.addl v (.Vlong (Integers.Int64.repr delta))
               else Val.add v (.Vint (Integers.Int.repr delta)))
      | .Bits _ _ _ _ => .Error "taking the address of a bitfield"
  | .Eparen r tycast _ => do
      let v ← constval ce r
      doCast v (Csyntax.typeof r) tycast
  | _ => .Error "not a compile-time constant"

/-- `Initializers.constval_cast` -/
def constvalCast (ce : CompositeEnv) (a : Csyntax.Expr) (ty : Ty) : Res Val := do
  let v ← constval ce a
  doCast v (Csyntax.typeof a) ty

/-! ## Building and recording initialization data -/

/-- `Initializers.state`: the initialization data generated so far
    (reversed), the position of its head, and the expected total size. -/
structure State where
  init : List InitData
  curr : Z
  total_size : Z

/-- `Initializers.initial_state` -/
def initialState (sz : Z) : State := ⟨[], 0, sz⟩

/-- `Initializers.int_of_byte` -/
def intOfByte (b : Integers.Byte) : Integers.Int := Integers.Int.repr (Integers.Byte.unsigned b)

/-- `Initializers.Init_byte` -/
def initByte (b : Integers.Byte) : InitData := .Init_int8 (intOfByte b)

/-- `Initializers.add_rev_bytes`: add a list of bytes to a reversed
    initialization data list. -/
def addRevBytes : List Integers.Byte → List InitData → List InitData
  | [], il => il
  | b :: l, il => addRevBytes l (initByte b :: il)

/-- `Initializers.add_zeros`: add `n` zero bytes. -/
def addZeros (n : Z) (il : List InitData) : List InitData :=
  List.replicate n.toNat (.Init_int8 Integers.Int.zero) ++ il

/-- `Initializers.normalize`: make sure the `depth` positions at the top of
    `il` are bytes. -/
def normalize : List InitData → Z → Res (List InitData)
  | il, depth =>
    if depth ≤ 0 then .OK il else
    match il with
    | [] => .Error "normalize: empty list"
    | .Init_int8 n :: il => do
        let il' ← normalize il (depth - 1)
        .OK (.Init_int8 n :: il')
    | .Init_int16 n :: il => do
        let il' ← normalize il (depth - 2)
        .OK (addRevBytes (encodeInt 2 (Integers.Int.unsigned n)) il')
    | .Init_int32 n :: il => do
        let il' ← normalize il (depth - 4)
        .OK (addRevBytes (encodeInt 4 (Integers.Int.unsigned n)) il')
    | .Init_int64 n :: il => do
        let il' ← normalize il (depth - 8)
        .OK (addRevBytes (encodeInt 8 (Integers.Int64.unsigned n)) il')
    | .Init_float32 f :: il => do
        let il' ← normalize il (depth - 4)
        .OK (addRevBytes (encodeInt 4 (Integers.Int.unsigned (Floats.Float32.toBits f))) il')
    | .Init_float64 f :: il => do
        let il' ← normalize il (depth - 8)
        .OK (addRevBytes (encodeInt 8 (Integers.Int64.unsigned (Floats.Float.toBits f))) il')
    | .Init_addrof _ _ :: _ => .Error "normalize: Init_addrof"
    | .Init_space n :: il =>
        let n := max 0 n
        if n ≤ depth then do
          let il' ← normalize il (depth - n)
          .OK (addZeros n il')
        else
          .OK (addZeros depth (.Init_space (n - depth) :: il))

/-- `Initializers.decompose_rec` -/
def decomposeRec : List Integers.Byte → List InitData → Z → Res (List Integers.Byte × List InitData)
  | accu, il, depth =>
    if depth ≤ 0 then .OK (accu, il) else
    match il with
    | .Init_int8 n :: il =>
        decomposeRec (Integers.Byte.repr (Integers.Int.unsigned n) :: accu) il (depth - 1)
    | _ => .Error "decompose: wrong shape"

/-- `Initializers.decompose`: split `il` into `depth` bytes (reversed) and the
    rest. -/
def decompose (il : List InitData) (depth : Z) : Res (List Integers.Byte × List InitData) :=
  decomposeRec [] il depth

/-- `Initializers.trisection`: `depth` bytes (reversed), `sz` bytes
    (reversed), and the remainder of the initialization list. -/
def trisection (il : List InitData) (depth sz : Z) :
    Res (List Integers.Byte × List Integers.Byte × List InitData) := do
  let il0 ← normalize il (depth + sz)
  let (bytes1, il1) ← decompose il0 depth
  let (bytes2, il2) ← decompose il1 sz
  .OK (bytes1, bytes2, il2)

/-- `Initializers.pad_to`: add padding so that position `pos` is within the
    state. -/
def padTo (s : State) (pos : Z) : State :=
  if pos ≤ s.curr then s
  else ⟨.Init_space (pos - s.curr) :: s.init, pos, s.total_size⟩

/-- `Initializers.store_data`: store `i` at position `pos`. -/
def storeData (s : State) (pos : Z) (i : InitData) : Res State :=
  let sz := i.size
  assertion (decide (0 ≤ pos) && decide (pos + sz ≤ s.total_size)) <|
  if s.curr ≤ pos then
    .OK ⟨i :: (if s.curr < pos then .Init_space (pos - s.curr) :: s.init else s.init),
      pos + sz, s.total_size⟩
  else
    let s' := padTo s (pos + sz)
    do
      let (bytes1, _, il2) ← trisection s'.init (s'.curr - (pos + sz)) sz
      .OK ⟨addRevBytes bytes1 (i :: il2), s'.curr, s'.total_size⟩

/-- `Initializers.init_data_for_carrier` -/
def initDataForCarrier (isz : IntSize) (n : Integers.Int) : InitData :=
  match isz with
  | .I8 | .IBool => .Init_int8 n
  | .I16 => .Init_int16 n
  | .I32 => .Init_int32 n

/-- `Initializers.store_int` -/
def storeInt (s : State) (pos : Z) (isz : IntSize) (n : Integers.Int) : Res State :=
  storeData s pos (initDataForCarrier isz n)

/-- `Initializers.load_int`: the integer of size `isz` at position `pos`. -/
def loadInt (s : State) (pos : Z) (isz : IntSize) : Res Integers.Int :=
  let chunk := Cop.chunkForCarrier isz
  let sz := sizeChunk chunk
  assertion (decide (0 ≤ pos) && decide (pos + sz ≤ s.total_size)) <|
  let s' := padTo s (pos + sz)
  do
    let (_, bytes2, _) ← trisection s'.init (s'.curr - (pos + sz)) sz
    .OK (Integers.Int.repr (decodeInt bytes2))

/-- `Initializers.init_data_list_of_state` -/
def initDataListOfState (s : State) : Res (List InitData) :=
  assertion (decide (s.curr ≤ s.total_size)) <|
  let s' := padTo s s.total_size
  .OK s'.init.reverse

/-! ## Translation of initializers -/

mutual
/-- `Initializers.initializer` -/
inductive Initializer where
  | Init_single (a : Csyntax.Expr)
  | Init_array (il : InitializerList)
  | Init_struct (il : InitializerList)
  | Init_union (f : Ident) (i : Initializer)

/-- `Initializers.initializer_list` -/
inductive InitializerList where
  | Init_nil
  | Init_cons (i : Initializer) (il : InitializerList)
end

/-- `Initializers.length_initializer_list` -/
def lengthInitializerList (il : InitializerList) : Z :=
  go 0 il
where
  go (accu : Z) : InitializerList → Z
    | .Init_nil => accu
    | .Init_cons _ il => go (accu + 1) il

/-- `Initializers.transl_init_single`: the initialization datum for a scalar
    variable of type `ty` initialized with `a`. -/
def translInitSingle (ce : CompositeEnv) (ty : Ty) (a : Csyntax.Expr) : Res InitData := do
  let v ← constvalCast ce a ty
  match v, ty with
  | .Vint n, .Tint .I8 _ _ | .Vint n, .Tint .IBool _ _ => .OK (.Init_int8 n)
  | .Vint n, .Tint .I16 _ _ => .OK (.Init_int16 n)
  | .Vint n, .Tint .I32 _ _ => .OK (.Init_int32 n)
  | .Vint n, .Tpointer _ _ => assertion (!Archi.ptr64) (.OK (.Init_int32 n))
  | .Vlong n, .Tlong _ _ => .OK (.Init_int64 n)
  | .Vlong n, .Tpointer _ _ => assertion Archi.ptr64 (.OK (.Init_int64 n))
  | .Vsingle f, .Tfloat .F32 _ => .OK (.Init_float32 f)
  | .Vfloat f, .Tfloat .F64 _ => .OK (.Init_float64 f)
  | .Vptr id ofs, .Tint .I32 _ _ => assertion (!Archi.ptr64) (.OK (.Init_addrof id ofs))
  | .Vptr id ofs, .Tlong _ _ => assertion Archi.ptr64 (.OK (.Init_addrof id ofs))
  | .Vptr id ofs, .Tpointer _ _ => .OK (.Init_addrof id ofs)
  | .Vundef, _ => .Error "undefined operation in initializer"
  | _, _ => .Error "type mismatch in initializer"

/-- `Initializers.transl_init_bitfield`: initialize the bitfield
    `Bits sz sg p w` at `pos` with `i`. -/
def translInitBitfield (ce : CompositeEnv) (s : State) (ty : Ty) (sz : IntSize) (p w : Z)
    (i : Initializer) (pos : Z) : Res State :=
  match i with
  | .Init_single a => do
      let v ← constvalCast ce a ty
      match v with
      | .Vint n => do
          let c ← loadInt s pos sz
          let c' := Integers.Int.bitfield_insert (Cop.firstBit sz p w).toNat w.toNat c n
          storeInt s pos sz c'
      | .Vundef => .Error "undefined operation in bitfield initializer"
      | _ => .Error "type mismatch in bitfield initializer"
  | _ => .Error "bitfield initialized by composite initializer"

/-- `Initializers.member_not_initialized`: padding bitfields and bitfields of
    zero width are not initialized. -/
def memberNotInitialized : Member → Bool
  | .Member_plain _ _ => false
  | .Member_bitfield _ _ _ _ w p => p || decide (w ≤ 0)

/-- The member search of the local `fix init` of
    `Initializers.transl_init_struct`: skip the members of `ms` that are not
    initialized (starting at bit position `pos`) and return the first
    initialized member, the members after it, and its bit position. -/
def skipUninitialized (ce : CompositeEnv) : List Member → Z → Option (Member × List Member × Z)
  | [], _ => none
  | m :: ms', pos =>
      if memberNotInitialized m then skipUninitialized ce ms' (nextField ce pos m)
      else some (m, ms', pos)

mutual
/-- `Initializers.transl_init_rec`: translate the initializer `i` for a
    variable of type `ty`, storing the data in `s` at position `pos`. -/
def translInitRec (ce : CompositeEnv) (s : State) (ty : Ty) (i : Initializer) (pos : Z) :
    Res State :=
  match i, ty with
  | .Init_single a, _ => do
      let d ← translInitSingle ce ty a
      storeData s pos d
  | .Init_array il, .Tarray tyelt nelt _ =>
      assertion (decide (lengthInitializerList il ≤ max 0 nelt)) <|
        translInitArray ce s tyelt il pos
  | .Init_struct il, .Tstruct id _ => do
      let co ← lookupComposite ce id
      match co.co_su with
      | .Struct => translInitStruct ce s co.co_members il pos 0
      | .Union => .Error "struct/union mismatch"
  | .Init_union f i1, .Tunion id _ => do
      let co ← lookupComposite ce id
      match co.co_su with
      | .Struct => .Error "union/struct mismatch"
      | .Union => do
          let ty1 ← fieldType f co.co_members
          let (delta, layout) ← unionFieldOffset ce f co.co_members
          match layout with
          | .Full => translInitRec ce s ty1 i1 (pos + delta)
          | .Bits sz _ p w => translInitBitfield ce s ty1 sz p w i1 (pos + delta)
  | _, _ => .Error "wrong type for compound initializer"

/-- `Initializers.transl_init_array` -/
def translInitArray (ce : CompositeEnv) (s : State) (tyelt : Ty) (il : InitializerList)
    (pos : Z) : Res State :=
  match il with
  | .Init_nil => .OK s
  | .Init_cons i1 il' => do
      let s1 ← translInitRec ce s tyelt i1 pos
      translInitArray ce s1 tyelt il' (pos + sizeof ce tyelt)

/-- `Initializers.transl_init_struct`: initialize the members `ms` (starting
    at bit position `pos`) with the initializers `il`. -/
def translInitStruct (ce : CompositeEnv) (s : State) (ms : List Member) (il : InitializerList)
    (base pos : Z) : Res State :=
  match il with
  | .Init_nil => .OK s
  | .Init_cons i1 il' =>
      match skipUninitialized ce ms pos with
      | none => .Error "too many elements in struct initializer"
      | some (m, ms', pos') => do
          let (delta, layout) ← layoutField ce pos' m
          let s1 ←
            match layout with
            | .Full => translInitRec ce s m.type i1 (base + delta)
            | .Bits sz _ p w => translInitBitfield ce s m.type sz p w i1 (base + delta)
          translInitStruct ce s1 ms' il' base (nextField ce pos' m)
end

/-- `Initializers.transl_init`: the initialization data for a variable of
    type `ty` with initializer `i`. -/
def translInit (ce : CompositeEnv) (ty : Ty) (i : Initializer) : Res (List InitData) := do
  let s0 := initialState (sizeof ce ty)
  let s1 ← translInitRec ce s0 ty i 0
  initDataListOfState s1

end Initializers
end CC
