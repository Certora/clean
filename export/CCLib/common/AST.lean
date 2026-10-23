/-
  Language-independent AST definitions — port of the definitional part of
  `common/AST.v` (799 lines, ~7 % proof).

  Moved here from `Clightdefs.lean` so that the semantic layers (`Values`,
  `Memdata`, `Memory`, `Events`) can depend on them without depending on the
  Clight AST.  All names are unchanged, so files emitted by `clightgen -lean`
  are unaffected.

  `Tptr`, `Xsize_t` and `Mptr` are the `Archi.ptr64`-dependent abbreviations
  CompCert uses to stay target-generic.
-/
import CCLib.lib.Positive
import CCLib.lib.Integers
import CCLib.lib.Floats

namespace CC

/-! ## Types of values -/

/-- `AST.typ` — the type of a value at the machine level. -/
inductive ATyp where
  | Tint | Tfloat | Tlong | Tsingle | Tany32 | Tany64
  deriving DecidableEq, Repr, Inhabited

/-- `AST.Tptr` -/
def Tptr : ATyp := if Archi.ptr64 then ATyp.Tlong else ATyp.Tint

/-- `AST.typesize` -/
def ATyp.size : ATyp → Z
  | .Tint => 4 | .Tfloat => 8 | .Tlong => 8
  | .Tsingle => 4 | .Tany32 => 4 | .Tany64 => 8

/-- `AST.xtype` — the more precise types used for arguments and results. -/
inductive XType where
  | Xbool | Xint8signed | Xint8unsigned | Xint16signed | Xint16unsigned
  | Xint | Xfloat | Xlong | Xsingle | Xptr | Xany32 | Xany64 | Xvoid
  deriving DecidableEq, Repr, Inhabited

/-- `AST.Xsize_t` -/
def Xsize_t : XType := if Archi.ptr64 then XType.Xlong else XType.Xint

/-- `AST.proj_xtype` -/
def XType.proj : XType → ATyp
  | .Xbool | .Xint8signed | .Xint8unsigned
  | .Xint16signed | .Xint16unsigned | .Xint => .Tint
  | .Xfloat => .Tfloat
  | .Xlong => .Tlong
  | .Xsingle => .Tsingle
  | .Xptr => Tptr
  | .Xany32 => .Tany32
  | .Xany64 => .Tany64
  | .Xvoid => .Tint

/-- `AST.inj_type` -/
def ATyp.inj : ATyp → XType
  | .Tint => .Xint | .Tfloat => .Xfloat | .Tlong => .Xlong
  | .Tsingle => .Xsingle | .Tany32 => .Xany32 | .Tany64 => .Xany64

/-! ## Memory chunks -/

/-- `AST.memory_chunk` — the quantity and type of a memory access. -/
inductive Chunk where
  | Mbool | Mint8signed | Mint8unsigned | Mint16signed | Mint16unsigned
  | Mint32 | Mint64 | Mfloat32 | Mfloat64 | Many32 | Many64
  deriving DecidableEq, Repr, Inhabited

/-- `AST.Mptr` — the chunk used to store a pointer. -/
def Mptr : Chunk := if Archi.ptr64 then Chunk.Mint64 else Chunk.Mint32

/-- `AST.type_of_chunk` -/
def Chunk.typ : Chunk → ATyp
  | .Mbool | .Mint8signed | .Mint8unsigned
  | .Mint16signed | .Mint16unsigned | .Mint32 => .Tint
  | .Mint64 => .Tlong
  | .Mfloat32 => .Tsingle
  | .Mfloat64 => .Tfloat
  | .Many32 => .Tany32
  | .Many64 => .Tany64

/-- `AST.xtype_of_chunk` -/
def Chunk.xtype : Chunk → XType
  | .Mbool => .Xbool | .Mint8signed => .Xint8signed | .Mint8unsigned => .Xint8unsigned
  | .Mint16signed => .Xint16signed | .Mint16unsigned => .Xint16unsigned
  | .Mint32 => .Xint | .Mint64 => .Xlong | .Mfloat32 => .Xsingle | .Mfloat64 => .Xfloat
  | .Many32 => .Xany32 | .Many64 => .Xany64

/-- `AST.chunk_of_type` -/
def Chunk.ofTyp : ATyp → Chunk
  | .Tint => .Mint32 | .Tfloat => .Mfloat64 | .Tlong => .Mint64
  | .Tsingle => .Mfloat32 | .Tany32 => .Many32 | .Tany64 => .Many64

/-! ## Calling conventions and signatures -/

/-- `AST.calling_convention` -/
structure CallConv where
  cc_vararg : Option Int
  cc_unproto : Bool
  cc_structret : Bool
  deriving DecidableEq, Repr, Inhabited

def cc_default : CallConv :=
  { cc_vararg := none, cc_unproto := false, cc_structret := false }

/-- `AST.signature` -/
structure Signature where
  sig_args : List XType
  sig_res : XType
  sig_cc : CallConv
  deriving DecidableEq, Repr, Inhabited

def mksignature (args : List XType) (res : XType) (cc : CallConv) : Signature :=
  { sig_args := args, sig_res := res, sig_cc := cc }

/-! ## External functions -/

/-- `AST.external_function` -/
inductive ExtFun where
  | EF_external (name : String) (sg : Signature)
  | EF_builtin (name : String) (sg : Signature)
  | EF_runtime (name : String) (sg : Signature)
  | EF_vload (chunk : Chunk)
  | EF_vstore (chunk : Chunk)
  | EF_malloc
  | EF_free
  | EF_memcpy (sz : Int) (al : Int)
  | EF_annot (kind : Positive) (text : String) (targs : List ATyp)
  | EF_annot_val (kind : Positive) (text : String) (targ : ATyp)
  | EF_inline_asm (text : String) (sg : Signature) (clobbers : List String)
  | EF_debug (kind : Positive) (text : Ident) (targs : List ATyp)
  deriving DecidableEq, Repr, Inhabited

/-- `AST.ef_sig` — the signature of an external function. -/
def ExtFun.sig : ExtFun → Signature
  | .EF_external _ sg | .EF_builtin _ sg | .EF_runtime _ sg => sg
  | .EF_vload chunk => mksignature [.Xptr] (Chunk.xtype chunk) cc_default
  | .EF_vstore chunk => mksignature [.Xptr, Chunk.xtype chunk] .Xvoid cc_default
  | .EF_malloc => mksignature [Xsize_t] .Xptr cc_default
  | .EF_free => mksignature [.Xptr] .Xvoid cc_default
  | .EF_memcpy _ _ => mksignature [.Xptr, .Xptr] .Xvoid cc_default
  | .EF_annot _ _ targs => mksignature (targs.map ATyp.inj) .Xvoid cc_default
  | .EF_annot_val _ _ targ => mksignature [targ.inj] targ.inj cc_default
  | .EF_inline_asm _ sg _ => sg
  | .EF_debug _ _ targs => mksignature (targs.map ATyp.inj) .Xvoid cc_default

/-! ## Global definitions -/

/-- `AST.init_data` -/
inductive InitData where
  | Init_int8 (n : Integers.Int)
  | Init_int16 (n : Integers.Int)
  | Init_int32 (n : Integers.Int)
  | Init_int64 (n : Integers.Int64)
  | Init_float32 (n : Floats.Float32)
  | Init_float64 (n : Floats.Float)
  | Init_space (n : Int)
  | Init_addrof (id : Ident) (ofs : Integers.Ptrofs)
  deriving DecidableEq, Repr, Inhabited

/-- `AST.init_data_size` -/
def InitData.size : InitData → Z
  | .Init_int8 _ => 1
  | .Init_int16 _ => 2
  | .Init_int32 _ => 4
  | .Init_int64 _ => 8
  | .Init_float32 _ => 4
  | .Init_float64 _ => 8
  | .Init_addrof _ _ => if Archi.ptr64 then 8 else 4
  | .Init_space n => max n 0

/-- `AST.init_data_list_size` -/
def InitData.listSize (l : List InitData) : Z :=
  l.foldr (fun i acc => i.size + acc) 0

/-- `AST.globvar V` -/
structure GlobVar (V : Type) where
  gvar_info : V
  gvar_init : List InitData
  gvar_readonly : Bool
  gvar_volatile : Bool

/-- `AST.globdef F V` -/
inductive GlobDef (F V : Type) where
  | Gfun (f : F)
  | Gvar (v : GlobVar V)

end CC
