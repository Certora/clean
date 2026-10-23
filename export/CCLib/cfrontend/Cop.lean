/-
  Semantics of C operators — port of `cfrontend/Cop.v` lines 1–1143, which is the
  whole operator semantics and contains **no proofs** in Rocq, so this is a
  direct transcription.  (The rest of Cop.v is memory-injection commutation,
  inversion lemmas, and the provably-dead `ArithConv` module.)

  Structure, following CompCert exactly: each operator first *classifies* its
  operand types (`classifyCast`, `classifyBinarith`, `classifyAdd`, …), then
  dispatches on that classification.  `semBinarith` casts both operands to the
  common arithmetic type before applying one of four callbacks.

  Memory shows up in exactly the places CompCert has it, and only to answer
  pointer-validity questions: `semCast`/`boolVal` need `weakValidPointer` when
  casting a pointer to `_Bool`, and `cmpPtr` needs `validPointer`.  Bitfield
  load/store additionally use `Mem.loadv`/`storev`.
-/
import CCLib.cfrontend.Ctypes
import CCLib.common.Memory

namespace CC

/-! ## Unary and binary operators (`Cop.unary_operation` / `binary_operation`) -/

/-- `Cop.unary_operation` -/
inductive Unop where
  | Onotbool | Onotint | Oneg | Oabsfloat
  deriving DecidableEq, Repr, Inhabited

/-- `Cop.binary_operation` -/
inductive Binop where
  | Oadd | Osub | Omul | Odiv | Omod | Oand | Oor | Oxor | Oshl | Oshr
  | Oeq | One | Olt | Ogt | Ole | Oge
  deriving DecidableEq, Repr, Inhabited

namespace Cop

/-! ## Casts -/

/-- `Cop.classify_cast_cases` -/
inductive CastCase where
  | pointer
  | i2i (sz : IntSize) (si : Signedness)
  | f2f | s2s | s2f | f2s
  | i2f (si : Signedness) | i2s (si : Signedness)
  | f2i (sz : IntSize) (si : Signedness) | s2i (sz : IntSize) (si : Signedness)
  | l2l | i2l (si : Signedness) | l2i (sz : IntSize) (si : Signedness)
  | l2f (si : Signedness) | l2s (si : Signedness)
  | f2l (si : Signedness) | s2l (si : Signedness)
  | i2bool | l2bool | f2bool | s2bool
  | struct (id1 id2 : Ident) | union (id1 id2 : Ident)
  | void | default

/-- `Cop.classify_cast` -/
def classifyCast (tfrom tto : Ty) : CastCase :=
  match tto, tfrom with
  | .Tvoid, _ => .void
  -- to int
  | .Tint sz2 si2 _, .Tint _ _ _ =>
      match sz2 with
      | .IBool => .i2bool
      | .I32 => if Archi.ptr64 then .i2i sz2 si2 else .pointer
      | _ => .i2i sz2 si2
  | .Tint sz2 si2 _, .Tlong _ _ =>
      if sz2 = .IBool then .l2bool else .l2i sz2 si2
  | .Tint sz2 si2 _, .Tfloat .F64 _ =>
      if sz2 = .IBool then .f2bool else .f2i sz2 si2
  | .Tint sz2 si2 _, .Tfloat .F32 _ =>
      if sz2 = .IBool then .s2bool else .s2i sz2 si2
  | .Tint sz2 si2 _, .Tpointer _ _
  | .Tint sz2 si2 _, .Tarray _ _ _
  | .Tint sz2 si2 _, .Tfunction _ _ _ =>
      if Archi.ptr64 then
        (if sz2 = .IBool then .l2bool else .l2i sz2 si2)
      else
        (match sz2 with
         | .IBool => .i2bool
         | .I32 => .pointer
         | _ => .i2i sz2 si2)
  -- to long
  | .Tlong _ _, .Tlong _ _ => if Archi.ptr64 then .pointer else .l2l
  | .Tlong _ _, .Tint _ si1 _ => .i2l si1
  | .Tlong si2 _, .Tfloat .F64 _ => .f2l si2
  | .Tlong si2 _, .Tfloat .F32 _ => .s2l si2
  | .Tlong si2 _, .Tpointer _ _
  | .Tlong si2 _, .Tarray _ _ _
  | .Tlong si2 _, .Tfunction _ _ _ => if Archi.ptr64 then .pointer else .i2l si2
  -- to float
  | .Tfloat .F64 _, .Tint _ si1 _ => .i2f si1
  | .Tfloat .F32 _, .Tint _ si1 _ => .i2s si1
  | .Tfloat .F64 _, .Tlong si1 _ => .l2f si1
  | .Tfloat .F32 _, .Tlong si1 _ => .l2s si1
  | .Tfloat .F64 _, .Tfloat .F64 _ => .f2f
  | .Tfloat .F32 _, .Tfloat .F32 _ => .s2s
  | .Tfloat .F64 _, .Tfloat .F32 _ => .s2f
  | .Tfloat .F32 _, .Tfloat .F64 _ => .f2s
  -- to pointer
  | .Tpointer _ _, .Tint _ si _ => if Archi.ptr64 then .i2l si else .pointer
  | .Tpointer _ _, .Tlong _ _ =>
      if Archi.ptr64 then .pointer else .l2i .I32 .Unsigned
  | .Tpointer _ _, .Tpointer _ _
  | .Tpointer _ _, .Tarray _ _ _
  | .Tpointer _ _, .Tfunction _ _ _ => .pointer
  -- to composite
  | .Tstruct id2 _, .Tstruct id1 _ => .struct id1 id2
  | .Tunion id2 _, .Tunion id1 _ => .union id1 id2
  | _, _ => .default

/-- `Cop.cast_int_int` — truncate/extend an int to a smaller size. -/
def castIntInt (sz : IntSize) (sg : Signedness) (i : Integers.Int) : Integers.Int :=
  match sz, sg with
  | .I8, .Signed => Integers.Int.sign_ext 8 i
  | .I8, .Unsigned => Integers.Int.zero_ext 8 i
  | .I16, .Signed => Integers.Int.sign_ext 16 i
  | .I16, .Unsigned => Integers.Int.zero_ext 16 i
  | .I32, _ => i
  | .IBool, _ => if Integers.Int.eq i Integers.Int.zero then Integers.Int.zero else Integers.Int.one

def castIntFloat : Signedness → Integers.Int → Floats.Float
  | .Signed, i => Floats.Float.ofInt i
  | .Unsigned, i => Floats.Float.ofIntu i
def castFloatInt : Signedness → Floats.Float → Option Integers.Int
  | .Signed, f => Floats.Float.toInt f
  | .Unsigned, f => Floats.Float.toIntu f
def castIntSingle : Signedness → Integers.Int → Floats.Float32
  | .Signed, i => Floats.Float32.ofInt i
  | .Unsigned, i => Floats.Float32.ofIntu i
def castSingleInt : Signedness → Floats.Float32 → Option Integers.Int
  | .Signed, f => Floats.Float32.toInt f
  | .Unsigned, f => Floats.Float32.toIntu f
def castIntLong : Signedness → Integers.Int → Integers.Int64
  | .Signed, i => Integers.Int64.repr (Integers.Int.signed i)
  | .Unsigned, i => Integers.Int64.repr (Integers.Int.unsigned i)
def castLongFloat : Signedness → Integers.Int64 → Floats.Float
  | .Signed, i => Floats.Float.ofLong i
  | .Unsigned, i => Floats.Float.ofLongu i
def castLongSingle : Signedness → Integers.Int64 → Floats.Float32
  | .Signed, i => Floats.Float32.ofLong i
  | .Unsigned, i => Floats.Float32.ofLongu i
def castFloatLong : Signedness → Floats.Float → Option Integers.Int64
  | .Signed, f => Floats.Float.toLong f
  | .Unsigned, f => Floats.Float.toLongu f
def castSingleLong : Signedness → Floats.Float32 → Option Integers.Int64
  | .Signed, f => Floats.Float32.toLong f
  | .Unsigned, f => Floats.Float32.toLongu f

/-- `Cop.sem_cast` -/
def semCast (v : Val) (t1 t2 : Ty) (m : Mem) : Option Val :=
  match classifyCast t1 t2 with
  | .pointer =>
      match v with
      | .Vptr _ _ => some v
      | .Vint _ => if Archi.ptr64 then none else some v
      | .Vlong _ => if Archi.ptr64 then some v else none
      | _ => none
  | .i2i sz2 si2 =>
      match v with | .Vint i => some (.Vint (castIntInt sz2 si2 i)) | _ => none
  | .f2f => match v with | .Vfloat f => some (.Vfloat f) | _ => none
  | .s2s => match v with | .Vsingle f => some (.Vsingle f) | _ => none
  | .s2f => match v with
            | .Vsingle f => some (.Vfloat (Floats.Float.ofSingle f)) | _ => none
  | .f2s => match v with
            | .Vfloat f => some (.Vsingle (Floats.Float.toSingle f)) | _ => none
  | .i2f si1 =>
      match v with | .Vint i => some (.Vfloat (castIntFloat si1 i)) | _ => none
  | .i2s si1 =>
      match v with | .Vint i => some (.Vsingle (castIntSingle si1 i)) | _ => none
  | .f2i sz2 si2 =>
      match v with
      | .Vfloat f =>
          match castFloatInt si2 f with
          | some i => some (.Vint (castIntInt sz2 si2 i))
          | none => none
      | _ => none
  | .s2i sz2 si2 =>
      match v with
      | .Vsingle f =>
          match castSingleInt si2 f with
          | some i => some (.Vint (castIntInt sz2 si2 i))
          | none => none
      | _ => none
  | .i2bool =>
      match v with
      | .Vint n => some (.Vint (if Integers.Int.eq n Integers.Int.zero then Integers.Int.zero else Integers.Int.one))
      | .Vptr b ofs =>
          if Archi.ptr64 then none
          else if Mem.weakValidPointer m b (Integers.Ptrofs.unsigned ofs)
               then some Val.Vone else none
      | _ => none
  | .l2bool =>
      match v with
      | .Vlong n =>
          some (.Vint (if Integers.Int64.eq n Integers.Int64.zero then Integers.Int.zero else Integers.Int.one))
      | .Vptr b ofs =>
          if !Archi.ptr64 then none
          else if Mem.weakValidPointer m b (Integers.Ptrofs.unsigned ofs)
               then some Val.Vone else none
      | _ => none
  | .f2bool =>
      match v with
      | .Vfloat f =>
          some (.Vint (if Floats.Float.cmp .Ceq f Floats.Float.zero
                       then Integers.Int.zero else Integers.Int.one))
      | _ => none
  | .s2bool =>
      match v with
      | .Vsingle f =>
          some (.Vint (if Floats.Float32.cmp .Ceq f Floats.Float32.zero
                       then Integers.Int.zero else Integers.Int.one))
      | _ => none
  | .l2l => match v with | .Vlong n => some (.Vlong n) | _ => none
  | .i2l si =>
      match v with | .Vint n => some (.Vlong (castIntLong si n)) | _ => none
  | .l2i sz si =>
      match v with
      | .Vlong n => some (.Vint (castIntInt sz si (Integers.Int.repr (Integers.Int64.unsigned n))))
      | _ => none
  | .l2f si1 =>
      match v with | .Vlong i => some (.Vfloat (castLongFloat si1 i)) | _ => none
  | .l2s si1 =>
      match v with
      | .Vlong i => some (.Vsingle (castLongSingle si1 i)) | _ => none
  | .f2l si2 =>
      match v with
      | .Vfloat f => match castFloatLong si2 f with
                     | some i => some (.Vlong i) | none => none
      | _ => none
  | .s2l si2 =>
      match v with
      | .Vsingle f => match castSingleLong si2 f with
                      | some i => some (.Vlong i) | none => none
      | _ => none
  | .struct id1 id2 =>
      match v with | .Vptr _ _ => if id1 = id2 then some v else none | _ => none
  | .union id1 id2 =>
      match v with | .Vptr _ _ => if id1 = id2 then some v else none | _ => none
  | .void => some v
  | .default => none

/-! ## Truth values -/

inductive BoolCase where
  | i | l | f | s | default

/-- `Cop.classify_bool` -/
def classifyBool (ty : Ty) : BoolCase :=
  match typeconv ty with
  | .Tint _ _ _ => .i
  | .Tpointer _ _ => if Archi.ptr64 then .l else .i
  | .Tfloat .F64 _ => .f
  | .Tfloat .F32 _ => .s
  | .Tlong _ _ => .l
  | _ => .default

/-- `Cop.bool_val` -/
def boolVal (v : Val) (t : Ty) (m : Mem) : Option Bool :=
  match classifyBool t with
  | .i =>
      match v with
      | .Vint n => some (!Integers.Int.eq n Integers.Int.zero)
      | .Vptr b ofs =>
          if Archi.ptr64 then none
          else if Mem.weakValidPointer m b (Integers.Ptrofs.unsigned ofs)
               then some true else none
      | _ => none
  | .l =>
      match v with
      | .Vlong n => some (!Integers.Int64.eq n Integers.Int64.zero)
      | .Vptr b ofs =>
          if !Archi.ptr64 then none
          else if Mem.weakValidPointer m b (Integers.Ptrofs.unsigned ofs)
               then some true else none
      | _ => none
  | .f =>
      match v with
      | .Vfloat f => some (!Floats.Float.cmp .Ceq f Floats.Float.zero)
      | _ => none
  | .s =>
      match v with
      | .Vsingle f => some (!Floats.Float32.cmp .Ceq f Floats.Float32.zero)
      | _ => none
  | .default => none

/-- `Cop.sem_notbool` -/
def semNotbool (v : Val) (ty : Ty) (m : Mem) : Option Val :=
  (boolVal v ty m).map (fun b => Val.ofBool (!b))

/-! ## Negation, complement, absolute value -/

inductive NegCase where
  | i (s : Signedness) | f | s | l (sg : Signedness) | default

/-- `Cop.classify_neg` -/
def classifyNeg : Ty → NegCase
  | .Tint .I32 .Unsigned _ => .i .Unsigned
  | .Tint _ _ _ => .i .Signed
  | .Tfloat .F64 _ => .f
  | .Tfloat .F32 _ => .s
  | .Tlong si _ => .l si
  | _ => .default

/-- `Cop.sem_neg` -/
def semNeg (v : Val) (ty : Ty) : Option Val :=
  match classifyNeg ty with
  | .i _ => match v with | .Vint n => some (.Vint (Integers.Int.neg n)) | _ => none
  | .f => match v with
          | .Vfloat f => some (.Vfloat (Floats.Float.neg f)) | _ => none
  | .s => match v with
          | .Vsingle f => some (.Vsingle (Floats.Float32.neg f)) | _ => none
  | .l _ => match v with | .Vlong n => some (.Vlong (Integers.Int64.neg n)) | _ => none
  | .default => none

/-- `Cop.sem_absfloat` — note the result is always a `double`. -/
def semAbsfloat (v : Val) (ty : Ty) : Option Val :=
  match classifyNeg ty with
  | .i sg =>
      match v with
      | .Vint n => some (.Vfloat (Floats.Float.abs (castIntFloat sg n)))
      | _ => none
  | .f => match v with
          | .Vfloat f => some (.Vfloat (Floats.Float.abs f)) | _ => none
  | .s => match v with
          | .Vsingle f =>
              some (.Vfloat (Floats.Float.abs (Floats.Float.ofSingle f)))
          | _ => none
  | .l sg =>
      match v with
      | .Vlong n => some (.Vfloat (Floats.Float.abs (castLongFloat sg n)))
      | _ => none
  | .default => none

inductive NotintCase where
  | i (s : Signedness) | l (s : Signedness) | default

/-- `Cop.classify_notint` -/
def classifyNotint : Ty → NotintCase
  | .Tint .I32 .Unsigned _ => .i .Unsigned
  | .Tint _ _ _ => .i .Signed
  | .Tlong si _ => .l si
  | _ => .default

/-- `Cop.sem_notint` -/
def semNotint (v : Val) (ty : Ty) : Option Val :=
  match classifyNotint ty with
  | .i _ => match v with | .Vint n => some (.Vint (Integers.Int.not n)) | _ => none
  | .l _ => match v with | .Vlong n => some (.Vlong (Integers.Int64.not n)) | _ => none
  | .default => none

/-! ## Binary arithmetic: the usual arithmetic conversions -/

inductive BinarithCase where
  | i (s : Signedness) | l (s : Signedness) | f | s | default

/-- `Cop.classify_binarith` -/
def classifyBinarith : Ty → Ty → BinarithCase
  | .Tint .I32 .Unsigned _, .Tint _ _ _ => .i .Unsigned
  | .Tint _ _ _, .Tint .I32 .Unsigned _ => .i .Unsigned
  | .Tint _ _ _, .Tint _ _ _ => .i .Signed
  | .Tlong .Signed _, .Tlong .Signed _ => .l .Signed
  | .Tlong _ _, .Tlong _ _ => .l .Unsigned
  | .Tlong sg _, .Tint _ _ _ => .l sg
  | .Tint _ _ _, .Tlong sg _ => .l sg
  | .Tfloat .F32 _, .Tfloat .F32 _ => .s
  | .Tfloat _ _, .Tfloat _ _ => .f
  | .Tfloat .F64 _, .Tint _ _ _ => .f
  | .Tfloat .F64 _, .Tlong _ _ => .f
  | .Tint _ _ _, .Tfloat .F64 _ => .f
  | .Tlong _ _, .Tfloat .F64 _ => .f
  | .Tfloat .F32 _, .Tint _ _ _ => .s
  | .Tfloat .F32 _, .Tlong _ _ => .s
  | .Tint _ _ _, .Tfloat .F32 _ => .s
  | .Tlong _ _, .Tfloat .F32 _ => .s
  | _, _ => .default

/-- `Cop.binarith_type` — the common type both operands are cast to. -/
def binarithType : BinarithCase → Ty
  | .i sg => .Tint .I32 sg noattr
  | .l sg => .Tlong sg noattr
  | .f => .Tfloat .F64 noattr
  | .s => .Tfloat .F32 noattr
  | .default => .Tvoid

/-- `Cop.sem_binarith` — cast both operands to the common type, then dispatch. -/
def semBinarith
    (semInt : Signedness → Integers.Int → Integers.Int → Option Val)
    (semLong : Signedness → Integers.Int64 → Integers.Int64 → Option Val)
    (semFloat : Floats.Float → Floats.Float → Option Val)
    (semSingle : Floats.Float32 → Floats.Float32 → Option Val)
    (v1 : Val) (t1 : Ty) (v2 : Val) (t2 : Ty) (m : Mem) : Option Val :=
  let c := classifyBinarith t1 t2
  let t := binarithType c
  match semCast v1 t1 t m with
  | none => none
  | some v1' =>
    match semCast v2 t2 t m with
    | none => none
    | some v2' =>
      match c with
      | .i sg => match v1', v2' with
                 | .Vint n1, .Vint n2 => semInt sg n1 n2
                 | _, _ => none
      | .l sg => match v1', v2' with
                 | .Vlong n1, .Vlong n2 => semLong sg n1 n2
                 | _, _ => none
      | .f => match v1', v2' with
              | .Vfloat n1, .Vfloat n2 => semFloat n1 n2
              | _, _ => none
      | .s => match v1', v2' with
              | .Vsingle n1, .Vsingle n2 => semSingle n1 n2
              | _, _ => none
      | .default => none

/-! ## Addition and subtraction (pointer arithmetic) -/

/-- `Cop.ptrofs_of_int` -/
def ptrofsOfInt : Signedness → Integers.Int → Integers.Ptrofs
  | .Signed, n => Integers.Ptrofs.of_ints n
  | .Unsigned, n => Integers.Ptrofs.of_intu n

inductive AddCase where
  | pi (ty : Ty) (si : Signedness) | pl (ty : Ty)
  | ip (si : Signedness) (ty : Ty) | lp (ty : Ty)
  | default

/-- `Cop.classify_add` -/
def classifyAdd (ty1 ty2 : Ty) : AddCase :=
  match typeconv ty1, typeconv ty2 with
  | .Tpointer ty _, .Tint _ si _ => .pi ty si
  | .Tpointer ty _, .Tlong _ _ => .pl ty
  | .Tint _ si _, .Tpointer ty _ => .ip si ty
  | .Tlong _ _, .Tpointer ty _ => .lp ty
  | _, _ => .default

inductive SubCase where
  | pi (ty : Ty) (si : Signedness) | pp (ty : Ty) | pl (ty : Ty) | default

/-- `Cop.classify_sub` -/
def classifySub (ty1 ty2 : Ty) : SubCase :=
  match typeconv ty1, typeconv ty2 with
  | .Tpointer ty _, .Tint _ si _ => .pi ty si
  | .Tpointer ty _, .Tpointer _ _ => .pp ty
  | .Tpointer ty _, .Tlong _ _ => .pl ty
  | _, _ => .default

/-- `Cop.sem_add_ptr_int` -/
def semAddPtrInt (cenv : CompositeEnv) (ty : Ty) (si : Signedness)
    (v1 v2 : Val) : Option Val :=
  match v1, v2 with
  | .Vptr b1 ofs1, .Vint n2 =>
      let n2' := ptrofsOfInt si n2
      some (.Vptr b1 (Integers.Ptrofs.add ofs1 (Integers.Ptrofs.mul (Integers.Ptrofs.repr (sizeof cenv ty)) n2')))
  | .Vint n1, .Vint n2 =>
      if Archi.ptr64 then none
      else some (.Vint (Integers.Int.add n1 (Integers.Int.mul (Integers.Int.repr (sizeof cenv ty)) n2)))
  | .Vlong n1, .Vint n2 =>
      let n2' := castIntLong si n2
      if Archi.ptr64
      then some (.Vlong (Integers.Int64.add n1 (Integers.Int64.mul (Integers.Int64.repr (sizeof cenv ty)) n2')))
      else none
  | _, _ => none

/-- `Cop.sem_add_ptr_long` -/
def semAddPtrLong (cenv : CompositeEnv) (ty : Ty) (v1 v2 : Val) : Option Val :=
  match v1, v2 with
  | .Vptr b1 ofs1, .Vlong n2 =>
      let n2' := Integers.Ptrofs.of_int64 n2
      some (.Vptr b1 (Integers.Ptrofs.add ofs1 (Integers.Ptrofs.mul (Integers.Ptrofs.repr (sizeof cenv ty)) n2')))
  | .Vint n1, .Vlong n2 =>
      let n2' := Integers.Int.repr (Integers.Int64.unsigned n2)
      if Archi.ptr64 then none
      else some (.Vint (Integers.Int.add n1 (Integers.Int.mul (Integers.Int.repr (sizeof cenv ty)) n2')))
  | .Vlong n1, .Vlong n2 =>
      if Archi.ptr64
      then some (.Vlong (Integers.Int64.add n1 (Integers.Int64.mul (Integers.Int64.repr (sizeof cenv ty)) n2)))
      else none
  | _, _ => none

/-- `Cop.sem_add` -/
def semAdd (cenv : CompositeEnv) (v1 : Val) (t1 : Ty) (v2 : Val) (t2 : Ty)
    (m : Mem) : Option Val :=
  match classifyAdd t1 t2 with
  | .pi ty si => semAddPtrInt cenv ty si v1 v2
  | .pl ty => semAddPtrLong cenv ty v1 v2
  | .ip si ty => semAddPtrInt cenv ty si v2 v1
  | .lp ty => semAddPtrLong cenv ty v2 v1
  | .default =>
      semBinarith
        (fun _ n1 n2 => some (.Vint (Integers.Int.add n1 n2)))
        (fun _ n1 n2 => some (.Vlong (Integers.Int64.add n1 n2)))
        (fun n1 n2 => some (.Vfloat (Floats.Float.add n1 n2)))
        (fun n1 n2 => some (.Vsingle (Floats.Float32.add n1 n2)))
        v1 t1 v2 t2 m

/-- `Cop.sem_sub` -/
def semSub (cenv : CompositeEnv) (v1 : Val) (t1 : Ty) (v2 : Val) (t2 : Ty)
    (m : Mem) : Option Val :=
  match classifySub t1 t2 with
  | .pi ty si =>
      match v1, v2 with
      | .Vptr b1 ofs1, .Vint n2 =>
          let n2' := ptrofsOfInt si n2
          some (.Vptr b1 (Integers.Ptrofs.sub ofs1
                  (Integers.Ptrofs.mul (Integers.Ptrofs.repr (sizeof cenv ty)) n2')))
      | .Vint n1, .Vint n2 =>
          if Archi.ptr64 then none
          else some (.Vint (Integers.Int.sub n1 (Integers.Int.mul (Integers.Int.repr (sizeof cenv ty)) n2)))
      | .Vlong n1, .Vint n2 =>
          let n2' := castIntLong si n2
          if Archi.ptr64
          then some (.Vlong (Integers.Int64.sub n1
                  (Integers.Int64.mul (Integers.Int64.repr (sizeof cenv ty)) n2')))
          else none
      | _, _ => none
  | .pl ty =>
      match v1, v2 with
      | .Vptr b1 ofs1, .Vlong n2 =>
          let n2' := Integers.Ptrofs.of_int64 n2
          some (.Vptr b1 (Integers.Ptrofs.sub ofs1
                  (Integers.Ptrofs.mul (Integers.Ptrofs.repr (sizeof cenv ty)) n2')))
      | .Vint n1, .Vlong n2 =>
          let n2' := Integers.Int.repr (Integers.Int64.unsigned n2)
          if Archi.ptr64 then none
          else some (.Vint (Integers.Int.sub n1 (Integers.Int.mul (Integers.Int.repr (sizeof cenv ty)) n2')))
      | .Vlong n1, .Vlong n2 =>
          if Archi.ptr64
          then some (.Vlong (Integers.Int64.sub n1
                  (Integers.Int64.mul (Integers.Int64.repr (sizeof cenv ty)) n2)))
          else none
      | _, _ => none
  | .pp ty =>
      match v1, v2 with
      | .Vptr b1 ofs1, .Vptr b2 ofs2 =>
          if b1 = b2 then
            let sz := sizeof cenv ty
            if 0 < sz && sz ≤ Integers.Ptrofs.max_signed
            then some (Val.Vptrofs (Integers.MI.divs (Integers.Ptrofs.sub ofs1 ofs2)
                                                     (Integers.Ptrofs.repr sz)))
            else none
          else none
      | _, _ => none
  | .default =>
      semBinarith
        (fun _ n1 n2 => some (.Vint (Integers.Int.sub n1 n2)))
        (fun _ n1 n2 => some (.Vlong (Integers.Int64.sub n1 n2)))
        (fun n1 n2 => some (.Vfloat (Floats.Float.sub n1 n2)))
        (fun n1 n2 => some (.Vsingle (Floats.Float32.sub n1 n2)))
        v1 t1 v2 t2 m

/-! ## Multiplicative and bitwise operators -/

def semMul (v1 : Val) (t1 : Ty) (v2 : Val) (t2 : Ty) (m : Mem) : Option Val :=
  semBinarith
    (fun _ n1 n2 => some (.Vint (Integers.Int.mul n1 n2)))
    (fun _ n1 n2 => some (.Vlong (Integers.Int64.mul n1 n2)))
    (fun n1 n2 => some (.Vfloat (Floats.Float.mul n1 n2)))
    (fun n1 n2 => some (.Vsingle (Floats.Float32.mul n1 n2)))
    v1 t1 v2 t2 m

def semDiv (v1 : Val) (t1 : Ty) (v2 : Val) (t2 : Ty) (m : Mem) : Option Val :=
  semBinarith
    (fun sg n1 n2 =>
      match sg with
      | .Signed =>
          if Integers.Int.eq n2 Integers.Int.zero
             || (Integers.Int.eq n1 (Integers.Int.repr Integers.Int.min_signed) && Integers.Int.eq n2 Integers.Int.mone)
          then none else some (.Vint (Integers.Int.divs n1 n2))
      | .Unsigned =>
          if Integers.Int.eq n2 Integers.Int.zero then none else some (.Vint (Integers.Int.divu n1 n2)))
    (fun sg n1 n2 =>
      match sg with
      | .Signed =>
          if Integers.Int64.eq n2 Integers.Int64.zero
             || (Integers.Int64.eq n1 (Integers.Int64.repr Integers.Int64.min_signed) && Integers.Int64.eq n2 Integers.Int64.mone)
          then none else some (.Vlong (Integers.Int64.divs n1 n2))
      | .Unsigned =>
          if Integers.Int64.eq n2 Integers.Int64.zero then none
          else some (.Vlong (Integers.Int64.divu n1 n2)))
    (fun n1 n2 => some (.Vfloat (Floats.Float.div n1 n2)))
    (fun n1 n2 => some (.Vsingle (Floats.Float32.div n1 n2)))
    v1 t1 v2 t2 m

def semMod (v1 : Val) (t1 : Ty) (v2 : Val) (t2 : Ty) (m : Mem) : Option Val :=
  semBinarith
    (fun sg n1 n2 =>
      match sg with
      | .Signed =>
          if Integers.Int.eq n2 Integers.Int.zero
             || (Integers.Int.eq n1 (Integers.Int.repr Integers.Int.min_signed) && Integers.Int.eq n2 Integers.Int.mone)
          then none else some (.Vint (Integers.Int.mods n1 n2))
      | .Unsigned =>
          if Integers.Int.eq n2 Integers.Int.zero then none else some (.Vint (Integers.Int.modu n1 n2)))
    (fun sg n1 n2 =>
      match sg with
      | .Signed =>
          if Integers.Int64.eq n2 Integers.Int64.zero
             || (Integers.Int64.eq n1 (Integers.Int64.repr Integers.Int64.min_signed) && Integers.Int64.eq n2 Integers.Int64.mone)
          then none else some (.Vlong (Integers.Int64.mods n1 n2))
      | .Unsigned =>
          if Integers.Int64.eq n2 Integers.Int64.zero then none
          else some (.Vlong (Integers.Int64.modu n1 n2)))
    (fun _ _ => none) (fun _ _ => none)
    v1 t1 v2 t2 m

def semAnd (v1 : Val) (t1 : Ty) (v2 : Val) (t2 : Ty) (m : Mem) : Option Val :=
  semBinarith
    (fun _ n1 n2 => some (.Vint (Integers.Int.and n1 n2)))
    (fun _ n1 n2 => some (.Vlong (Integers.Int64.and n1 n2)))
    (fun _ _ => none) (fun _ _ => none) v1 t1 v2 t2 m

def semOr (v1 : Val) (t1 : Ty) (v2 : Val) (t2 : Ty) (m : Mem) : Option Val :=
  semBinarith
    (fun _ n1 n2 => some (.Vint (Integers.Int.or n1 n2)))
    (fun _ n1 n2 => some (.Vlong (Integers.Int64.or n1 n2)))
    (fun _ _ => none) (fun _ _ => none) v1 t1 v2 t2 m

def semXor (v1 : Val) (t1 : Ty) (v2 : Val) (t2 : Ty) (m : Mem) : Option Val :=
  semBinarith
    (fun _ n1 n2 => some (.Vint (Integers.Int.xor n1 n2)))
    (fun _ n1 n2 => some (.Vlong (Integers.Int64.xor n1 n2)))
    (fun _ _ => none) (fun _ _ => none) v1 t1 v2 t2 m

/-! ## Shifts

Shifts do *not* go through `semBinarith`: C does not convert the two operands to
a common type, and the shift amount is range-checked instead. -/

inductive ShiftCase where
  | ii (s : Signedness) | ll (s : Signedness)
  | il (s : Signedness) | li (s : Signedness) | default

/-- `Cop.classify_shift` -/
def classifyShift (ty1 ty2 : Ty) : ShiftCase :=
  match typeconv ty1, typeconv ty2 with
  | .Tint .I32 .Unsigned _, .Tint _ _ _ => .ii .Unsigned
  | .Tint _ _ _, .Tint _ _ _ => .ii .Signed
  | .Tint .I32 .Unsigned _, .Tlong _ _ => .il .Unsigned
  | .Tint _ _ _, .Tlong _ _ => .il .Signed
  | .Tlong s _, .Tint _ _ _ => .li s
  | .Tlong s _, .Tlong _ _ => .ll s
  | _, _ => .default

/-- `Cop.sem_shift` -/
def semShift
    (semInt : Signedness → Integers.Int → Integers.Int → Integers.Int)
    (semLong : Signedness → Integers.Int64 → Integers.Int64 → Integers.Int64)
    (v1 : Val) (t1 : Ty) (v2 : Val) (t2 : Ty) : Option Val :=
  match classifyShift t1 t2 with
  | .ii sg =>
      match v1, v2 with
      | .Vint n1, .Vint n2 =>
          if Integers.Int.ltu n2 Integers.Int.iwordsize then some (.Vint (semInt sg n1 n2)) else none
      | _, _ => none
  | .il sg =>
      match v1, v2 with
      | .Vint n1, .Vlong n2 =>
          if Integers.Int64.ltu n2 (Integers.Int64.repr 32)
          then some (.Vint (semInt sg n1 (Integers.Int64.loword n2))) else none
      | _, _ => none
  | .li sg =>
      match v1, v2 with
      | .Vlong n1, .Vint n2 =>
          if Integers.Int.ltu n2 (Integers.Int.repr 64)
          then some (.Vlong (semLong sg n1 (Integers.Int64.repr (Integers.Int.unsigned n2))))
          else none
      | _, _ => none
  | .ll sg =>
      match v1, v2 with
      | .Vlong n1, .Vlong n2 =>
          if Integers.Int64.ltu n2 Integers.Int64.iwordsize
          then some (.Vlong (semLong sg n1 n2)) else none
      | _, _ => none
  | .default => none

def semShl (v1 : Val) (t1 : Ty) (v2 : Val) (t2 : Ty) : Option Val :=
  semShift (fun _ n1 n2 => Integers.Int.shl n1 n2) (fun _ n1 n2 => Integers.Int64.shl n1 n2)
    v1 t1 v2 t2

def semShr (v1 : Val) (t1 : Ty) (v2 : Val) (t2 : Ty) : Option Val :=
  semShift
    (fun sg n1 n2 => match sg with
                     | .Signed => Integers.Int.shr n1 n2 | .Unsigned => Integers.Int.shru n1 n2)
    (fun sg n1 n2 => match sg with
                     | .Signed => Integers.Int64.shr n1 n2 | .Unsigned => Integers.Int64.shru n1 n2)
    v1 t1 v2 t2

/-! ## Comparisons -/

inductive CmpCase where
  | pp | pi (si : Signedness) | ip (si : Signedness) | pl | lp | default

/-- `Cop.classify_cmp` -/
def classifyCmp (ty1 ty2 : Ty) : CmpCase :=
  match typeconv ty1, typeconv ty2 with
  | .Tpointer _ _, .Tpointer _ _ => .pp
  | .Tpointer _ _, .Tint _ si _ => .pi si
  | .Tint _ si _, .Tpointer _ _ => .ip si
  | .Tpointer _ _, .Tlong _ _ => .pl
  | .Tlong _ _, .Tpointer _ _ => .lp
  | _, _ => .default

/-- `Cop.cmp_ptr` — pointer comparison, using the memory's validity predicate. -/
def cmpPtr (m : Mem) (c : Comparison) (v1 v2 : Val) : Option Val :=
  (if Archi.ptr64
   then Val.cmplu_bool (Mem.validPointer m) c v1 v2
   else Val.cmpu_bool (Mem.validPointer m) c v1 v2).map Val.ofBool

/-- `Cop.sem_cmp` -/
def semCmp (c : Comparison) (v1 : Val) (t1 : Ty) (v2 : Val) (t2 : Ty)
    (m : Mem) : Option Val :=
  match classifyCmp t1 t2 with
  | .pp => cmpPtr m c v1 v2
  | .pi si =>
      match v2 with
      | .Vint n2 => cmpPtr m c v1 (Val.Vptrofs (ptrofsOfInt si n2))
      | .Vptr _ _ => if Archi.ptr64 then none else cmpPtr m c v1 v2
      | _ => none
  | .ip si =>
      match v1 with
      | .Vint n1 => cmpPtr m c (Val.Vptrofs (ptrofsOfInt si n1)) v2
      | .Vptr _ _ => if Archi.ptr64 then none else cmpPtr m c v1 v2
      | _ => none
  | .pl =>
      match v2 with
      | .Vlong n2 => cmpPtr m c v1 (Val.Vptrofs (Integers.Ptrofs.of_int64 n2))
      | .Vptr _ _ => if Archi.ptr64 then cmpPtr m c v1 v2 else none
      | _ => none
  | .lp =>
      match v1 with
      | .Vlong n1 => cmpPtr m c (Val.Vptrofs (Integers.Ptrofs.of_int64 n1)) v2
      | .Vptr _ _ => if Archi.ptr64 then cmpPtr m c v1 v2 else none
      | _ => none
  | .default =>
      semBinarith
        (fun sg n1 n2 => some (Val.ofBool (match sg with
            | .Signed => Integers.Int.cmp c n1 n2
            | .Unsigned => Integers.Int.cmpu c n1 n2)))
        (fun sg n1 n2 => some (Val.ofBool (match sg with
            | .Signed => Integers.Int64.cmp c n1 n2
            | .Unsigned => Integers.Int64.cmpu c n1 n2)))
        (fun n1 n2 => some (Val.ofBool (Floats.Float.cmp c n1 n2)))
        (fun n1 n2 => some (Val.ofBool (Floats.Float32.cmp c n1 n2)))
        v1 t1 v2 t2 m

/-! ## Switch arguments -/

inductive SwitchCase where
  | i | l | default

/-- `Cop.classify_switch` -/
def classifySwitch : Ty → SwitchCase
  | .Tint _ _ _ => .i
  | .Tlong _ _ => .l
  | _ => .default

/-- `Cop.sem_switch_arg` -/
def semSwitchArg (v : Val) (ty : Ty) : Option Z :=
  match classifySwitch ty with
  | .i => match v with | .Vint n => some (Integers.Int.unsigned n) | _ => none
  | .l => match v with | .Vlong n => some (Integers.Int64.unsigned n) | _ => none
  | .default => none

/-! ## Top-level dispatch -/

/-- `Cop.sem_unary_operation` -/
def semUnaryOperation (op : Unop) (v : Val) (ty : Ty) (m : Mem) : Option Val :=
  match op with
  | .Onotbool => semNotbool v ty m
  | .Onotint => semNotint v ty
  | .Oneg => semNeg v ty
  | .Oabsfloat => semAbsfloat v ty

/-- `Cop.sem_binary_operation` -/
def semBinaryOperation (cenv : CompositeEnv) (op : Binop)
    (v1 : Val) (t1 : Ty) (v2 : Val) (t2 : Ty) (m : Mem) : Option Val :=
  match op with
  | .Oadd => semAdd cenv v1 t1 v2 t2 m
  | .Osub => semSub cenv v1 t1 v2 t2 m
  | .Omul => semMul v1 t1 v2 t2 m
  | .Omod => semMod v1 t1 v2 t2 m
  | .Odiv => semDiv v1 t1 v2 t2 m
  | .Oand => semAnd v1 t1 v2 t2 m
  | .Oor => semOr v1 t1 v2 t2 m
  | .Oxor => semXor v1 t1 v2 t2 m
  | .Oshl => semShl v1 t1 v2 t2
  | .Oshr => semShr v1 t1 v2 t2
  | .Oeq => semCmp .Ceq v1 t1 v2 t2 m
  | .One => semCmp .Cne v1 t1 v2 t2 m
  | .Olt => semCmp .Clt v1 t1 v2 t2 m
  | .Ogt => semCmp .Cgt v1 t1 v2 t2 m
  | .Ole => semCmp .Cle v1 t1 v2 t2 m
  | .Oge => semCmp .Cge v1 t1 v2 t2 m

/-! ## Bitfield access

`Cop.load_bitfield` / `store_bitfield` are *relations* in Rocq (they constrain
the position and width), and `Clight`'s `deref_loc`/`assign_loc` use them for the
`Bits` case.  The carrier is read and written with a whole-integer chunk; the
field is then extracted or spliced. -/

/-- `Cop.chunk_for_carrier` -/
def chunkForCarrier : IntSize → Chunk
  | .I8 | .IBool => .Mint8unsigned
  | .I16 => .Mint16unsigned
  | .I32 => .Mint32

/-- `Cop.bitsize_carrier` -/
def bitsizeCarrier : IntSize → Z
  | .I8 | .IBool => 8
  | .I16 => 16
  | .I32 => 32

/-- `Cop.first_bit` — bit index of the field within its carrier. -/
def firstBit (sz : IntSize) (pos width : Z) : Z :=
  if Archi.big_endian then bitsizeCarrier sz - pos - width else pos

/-- `Cop.bitfield_extract` -/
def bitfieldExtract (sz : IntSize) (sg : Signedness) (pos width : Z)
    (c : Integers.Int) : Integers.Int :=
  if sz = .IBool || sg = .Unsigned
  then Integers.Int.unsigned_bitfield_extract (firstBit sz pos width).toNat width.toNat c
  else Integers.Int.signed_bitfield_extract (firstBit sz pos width).toNat width.toNat c

/-- `Cop.bitfield_normalize` -/
def bitfieldNormalize (sz : IntSize) (sg : Signedness) (width : Z)
    (n : Integers.Int) : Integers.Int :=
  if sz = .IBool || sg = .Unsigned
  then Integers.Int.zero_ext width.toNat n
  else Integers.Int.sign_ext width.toNat n

/-- `Cop.load_bitfield` -/
inductive LoadBitfield :
    Ty → IntSize → Signedness → Z → Z → Mem → Val → Val → Prop where
  | intro (sz sg1 attr sg pos width m addr c) :
      0 ≤ pos → 0 < width → width ≤ bitsizeIntsize sz →
      pos + width ≤ bitsizeCarrier sz →
      sg1 = (if width < bitsizeIntsize sz then Signedness.Signed else sg) →
      Mem.loadv (chunkForCarrier sz) m addr = some (.Vint c) →
      LoadBitfield (.Tint sz sg1 attr) sz sg pos width m addr
        (.Vint (bitfieldExtract sz sg pos width c))

/-- `Cop.store_bitfield` -/
inductive StoreBitfield :
    Ty → IntSize → Signedness → Z → Z → Mem → Val → Val → Mem → Val → Prop where
  | intro (sz sg1 attr sg pos width m addr c n m') :
      0 ≤ pos → 0 < width → width ≤ bitsizeIntsize sz →
      pos + width ≤ bitsizeCarrier sz →
      sg1 = (if width < bitsizeIntsize sz then Signedness.Signed else sg) →
      Mem.loadv (chunkForCarrier sz) m addr = some (.Vint c) →
      Mem.storev (chunkForCarrier sz) m addr
        (.Vint (Integers.Int.bitfield_insert (firstBit sz pos width).toNat
                  width.toNat c n)) = some m' →
      StoreBitfield (.Tint sz sg1 attr) sz sg pos width m addr (.Vint n)
        m' (.Vint (bitfieldNormalize sz sg width n))

/-- `Cop.classify_fun` — used by `Clight`'s `step_call`. -/
inductive FunCase where
  | f (targs : List Ty) (tres : Ty) (cc : CallConv)
  | default

def classifyFun : Ty → FunCase
  | .Tfunction args res cc => .f args res cc
  | .Tpointer (.Tfunction args res cc) _ => .f args res cc
  | _ => .default

end Cop
end CC
