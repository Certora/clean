/-
  Expansion of built-ins and pseudo-instructions for PowerPC — port of
  `powerpc/Asmexpand.ml`.

  `Asmexpand` runs after the verified compiler, on the generated `Asm`
  program: it replaces the pseudo-instructions (`Pallocframe`,
  `Pfreeframe`, `Pextzw`, `Pfcfl`, `Pfcti`, `Pfctid`, `Pfmake`, `Pfxdp`,
  `Pisel`, `Pfsel_gen`, `Plmake`, `Pllo`, `Plhi`, `Pmfcrbit`) by machine
  instructions, expands the built-in functions that are inlined (`memcpy`,
  volatile loads and stores, `va_start`, byte swaps, cache control, special
  registers, atomic operations, …), sets condition bit 6 before calls to
  variadic functions, and relaxes conditional branches whose target is out
  of range.  Like the OCaml code, it is not verified.

  Differences from OCaml:
  * The configuration (`Archi.ppc64`, `eref` i.e. `Configuration.model =
    "e5500"`, `Clflags.option_ffpu`, `Clflags.option_Osize`,
    `Configuration.system = "diab"`, the linker parameters used by
    `Asmgen.aglobal`/`abased`, and the atom `intern_string
    "__compcert_va_saveregs"`) is the argument `Asmexpand.Options`.
  * The global references `linkregister_offset`, `retaddr_offset` and
    `current_function_stacksize` are the state `PState`, threaded by the
    monad `PM` on top of the expansion monad `Asmexpandaux.M`; the loop of
    `Asmexpandaux.expand` (without `-g`) is re-done in `PM` (`expandCode`).
  * `raise (Error s)`, `assert false` and `invalid_arg` become errors of the
    monad.
  * Not ported: the DWARF register numbering (`int_reg_to_dwarf`,
    `float_reg_to_dwarf`, `preg_to_dwarf`), which only serves `-g`.
-/
import CCLib.powerpc.Asmgen
import CCLib.backend.Asmexpandaux

namespace CC
namespace PowerPC
namespace Asmexpand

open Asm Asmexpandaux

instance : AsmInstr Instruction where
  labelOf | .Plabel l => some l | _ => none
  mkLabel := .Plabel
  annotKind | .Pbuiltin (.EF_annot kind _ _) _ _ => some kind | _ => none
  isDebug | .Pbuiltin (.EF_debug _ _ _) _ _ => true | _ => false
  mkBuiltin ef := .Pbuiltin ef [] .BR_none

/-- The expansion monad for PowerPC code. -/
abbrev EM := Asmexpandaux.M Instruction

/-- The configuration used by the expansion. -/
structure Options where
  /-- `Archi.ppc64` -/
  ppc64 : Bool := false
  /-- `eref` (FreeScale's EREF extensions: `Configuration.model = "e5500"`) -/
  eref : Bool := false
  /-- `Clflags.option_ffpu` -/
  ffpu : Bool := true
  /-- `Clflags.option_Osize` -/
  osize : Bool := false
  /-- `Configuration.system = "diab"` (comment syntax of inline assembly) -/
  diab : Bool := false
  /-- the linker parameters (`symbol_is_small_data`, …) used by `Asmgen` -/
  linker : LinkerParams
  /-- `intern_string "__compcert_va_saveregs"` -/
  vaSaveregs : Ident

/-- The global references of `Asmexpand.ml`. -/
structure PState where
  /-- `linkregister_offset` -/
  linkOfs : Integers.Int := 0
  /-- `retaddr_offset` -/
  retOfs : Integers.Int := 0

/-- The PowerPC expansion monad. -/
abbrev PM := StateT PState EM

/-- `raise (Error s)` -/
def err {α : Type} (s : String) : PM α := throw s

/-- `emit` -/
def em (i : Instruction) : PM Unit := (emit i : EM Unit)

/-- `new_label` -/
def newLbl : PM Label := (newLabel : EM Label)

/-- Emit a list of instructions. -/
def emitAll (l : List Instruction) : PM Unit := for i in l do em i

/-- `Int.repr` -/
abbrev I (n : Int) : Integers.Int := Integers.Int.repr n
/-- `Int64.repr` -/
abbrev L (n : Int) : Integers.Int64 := Integers.Int64.repr n

/-- A pointer offset as a 32-bit integer. -/
def ofsInt (n : Integers.Ptrofs) : Integers.Int := Integers.Int.repr (Integers.Ptrofs.unsigned n)

/-- `upper32` -/
def upper32 : Integers.Int64 := L 0xFFFFFFFF00000000
/-- `lower32` -/
def lower32 : Integers.Int64 := L 0x00000000FFFFFFFF

/-- `emit_loadimm` -/
def emitLoadimm (r : Ireg) (n : Integers.Int) : PM Unit := emitAll (Asmgen.loadimm r n [])
/-- `emit_addimm` -/
def emitAddimm (rd rs : Ireg) (n : Integers.Int) : PM Unit := emitAll (Asmgen.addimm rd rs n [])

/-- `num_crbit` -/
def numCrbit : Crbit → Nat
  | .CRbit_0 => 0 | .CRbit_1 => 1 | .CRbit_2 => 2 | .CRbit_3 => 3 | .CRbit_6 => 6

/-! ## Annotations -/

/-- `Asmexpand.expand_annot_val` -/
def expandAnnotVal (kind : Positive) (txt : String) (targ : ATyp) (args : List (BuiltinArg Preg))
    (res : BuiltinRes Preg) : PM Unit := do
  em (.Pbuiltin (.EF_annot kind txt [targ]) args .BR_none)
  match args, res with
  | [.BA (.IR src)], .BR (.IR dst) => if dst ≠ src then em (.Pmr dst src)
  | [.BA (.FR src)], .BR (.FR dst) => if dst ≠ src then em (.Pfmr dst src)
  | _, _ => err "ill-formed __builtin_annot_intval"

/-! ## `memcpy`

Unaligned accesses to 16- and 32-bit integers are fast, but unaligned
accesses to 64-bit floats can be slow: 64-bit accesses are used only if the
alignment is at least 4. -/

/-- `Asmexpand.offset_in_range` -/
def offsetInRange (ofs : Integers.Int) : Bool := Integers.Int.eq (Asmgen.highS ofs) 0

/-- `Asmexpand.memcpy_small_arg` -/
def memcpySmallArg (sz : Int) (arg : BuiltinArg Preg) (tmp : Ireg) : PM (Ireg × Integers.Int) :=
  match arg with
  | .BA (.IR r) => return (r, 0)
  | .BA_addrstack ofs =>
    let ofs := ofsInt ofs
    if offsetInRange ofs && offsetInRange (Integers.Int.add ofs (I sz)) then return (.GPR1, ofs)
    else do
      emitAddimm tmp .GPR1 ofs
      return (tmp, 0)
  | _ => err "memcpy_small_arg"

/-- `Asmexpand.expand_builtin_memcpy_small` -/
def expandBuiltinMemcpySmall (o : Options) (sz al : Int) (src dst : BuiltinArg Preg) : PM Unit := do
  let tsrc : Ireg := if dst ≠ .BA (.IR .GPR11) then .GPR11 else .GPR12
  let tdst : Ireg := if src ≠ .BA (.IR .GPR12) then .GPR12 else .GPR11
  let (rsrc, osrc) ← memcpySmallArg sz src tsrc
  let (rdst, odst) ← memcpySmallArg sz dst tdst
  let add := fun (x : Integers.Int) (k : Int) => Integers.Int.add x (I k)
  let rec copy (fuel : Nat) (osrc odst : Integers.Int) (sz : Int) : PM Unit :=
    match fuel with
    | 0 => pure ()
    | fuel + 1 =>
      if sz ≥ 8 && al ≥ 4 && o.ffpu then do
        em (.Plfd .FPR13 (.Cint osrc) rsrc); em (.Pstfd .FPR13 (.Cint odst) rdst)
        copy fuel (add osrc 8) (add odst 8) (sz - 8)
      else if sz ≥ 4 then do
        em (.Plwz .GPR0 (.Cint osrc) rsrc); em (.Pstw .GPR0 (.Cint odst) rdst)
        copy fuel (add osrc 4) (add odst 4) (sz - 4)
      else if sz ≥ 2 then do
        em (.Plhz .GPR0 (.Cint osrc) rsrc); em (.Psth .GPR0 (.Cint odst) rdst)
        copy fuel (add osrc 2) (add odst 2) (sz - 2)
      else if sz ≥ 1 then do
        em (.Plbz .GPR0 (.Cint osrc) rsrc); em (.Pstb .GPR0 (.Cint odst) rdst)
        copy fuel (add osrc 1) (add odst 1) (sz - 1)
      else pure ()
  copy (sz.toNat + 1) osrc odst sz

/-- `Asmexpand.memcpy_big_arg`: set `tmp` to the value of `arg` minus 4. -/
def memcpyBigArg (arg : BuiltinArg Preg) (tmp : Ireg) : PM Unit :=
  match arg with
  | .BA (.IR r) => em (.Paddi tmp r (.Cint (I (-4))))
  | .BA_addrstack ofs => emitAddimm tmp .GPR1 (Integers.Int.add (ofsInt ofs) (I (-4)))
  | _ => err "memcpy_big_arg"

/-- `Asmexpand.expand_builtin_memcpy_big` -/
def expandBuiltinMemcpyBig (sz : Int) (src dst : BuiltinArg Preg) : PM Unit := do
  if sz < 4 then err "expand_builtin_memcpy_big"
  emitLoadimm .GPR0 (I (sz / 4))
  em (.Pmtctr .GPR0)
  let (s, d) : Ireg × Ireg := if dst ≠ .BA (.IR .GPR11) then (.GPR11, .GPR12) else (.GPR12, .GPR11)
  memcpyBigArg src s
  memcpyBigArg dst d
  let lbl ← newLbl
  em (.Plabel lbl)
  em (.Plwzu .GPR0 (.Cint (I 4)) s)
  em (.Pstwu .GPR0 (.Cint (I 4)) d)
  em (.Pbdnz lbl)
  -- s and d lag behind by 4 bytes
  match sz % 4 with
  | 1 => do em (.Plbz .GPR0 (.Cint (I 4)) s); em (.Pstb .GPR0 (.Cint (I 4)) d)
  | 2 => do em (.Plhz .GPR0 (.Cint (I 4)) s); em (.Psth .GPR0 (.Cint (I 4)) d)
  | 3 => do
    em (.Plhz .GPR0 (.Cint (I 4)) s); em (.Psth .GPR0 (.Cint (I 4)) d)
    em (.Plbz .GPR0 (.Cint (I 6)) s); em (.Pstb .GPR0 (.Cint (I 6)) d)
  | _ => pure ()

/-- `Asmexpand.expand_builtin_memcpy` -/
def expandBuiltinMemcpy (o : Options) (sz al : Int) (args : List (BuiltinArg Preg)) : PM Unit :=
  match args with
  | [dst, src] =>
    let limit := if o.ffpu && al ≥ 4 then (if o.osize then 35 else 51)
      else (if o.osize then 19 else 27)
    if sz ≤ limit then expandBuiltinMemcpySmall o sz al src dst
    else expandBuiltinMemcpyBig sz src dst
  | _ => err "expand_builtin_memcpy"

/-! ## Volatile reads and writes -/

/-- The instruction builders passed to `expand_volatile_access`. -/
abbrev Mk1 := Constant → Ireg → Code → Code
/-- The instruction builders (two index registers). -/
abbrev Mk2 := Ireg → Ireg → Code → Code

/-- `Asmexpand.expand_volatile_access` -/
def expandVolatileAccess (o : Options) (mk1 : Mk1) (mk2 : Mk2) (ofsUnaligned : Bool)
    (addr : BuiltinArg Preg) (temp : Ireg) : PM Unit :=
  match addr with
  | .BA (.IR r) => emitAll (mk1 (.Cint 0) r [])
  | .BA_addrstack ofs => emitAll (Asmgen.ainstack mk1 mk2 ofsUnaligned temp (ofsInt ofs) [])
  | .BA_addrglobal id ofs => emitAll (Asmgen.aglobal o.linker mk1 mk2 ofsUnaligned temp id ofs [])
  | .BA_addptr (.BA (.IR r)) (.BA_int n) =>
    emitAll (Asmgen.aindexed mk1 mk2 ofsUnaligned r temp n [])
  | .BA_addptr (.BA_addrglobal id ofs) (.BA (.IR r)) =>
    emitAll (Asmgen.abased o.linker mk1 mk2 ofsUnaligned r temp id ofs [])
  | .BA_addptr (.BA (.IR r1)) (.BA (.IR r2)) => emitAll (Asmgen.aindexed2 mk2 r1 r2 [])
  | _ => err "expand_volatile_access"

/-- `Asmexpand.offset_constant` -/
def offsetConstant (cst : Constant) (delta : Integers.Int) : Option Constant :=
  match cst with
  | .Cint n =>
    let n' := Integers.Int.add n delta
    if offsetInRange n' then some (.Cint n') else none
  | .Csymbol_sda id ofs =>
    some (.Csymbol_sda id (Integers.Ptrofs.add ofs (Integers.Ptrofs.repr (Integers.Int.signed delta))))
  | _ => none

/-- `Asmexpand.expand_load_int64` -/
def expandLoadInt64 (hi lo base : Ireg) (ofsHi ofsLo : Constant) (k : Code) : Code :=
  if hi ≠ base then .Plwz hi ofsHi base :: .Plwz lo ofsLo base :: k
  else .Plwz lo ofsLo base :: .Plwz hi ofsHi base :: k

/-- `Asmexpand.expand_builtin_vload_1` -/
def expandBuiltinVload1 (o : Options) (chunk : Chunk) (addr : BuiltinArg Preg)
    (res : BuiltinRes Preg) : PM Unit :=
  let va := expandVolatileAccess o
  match chunk, res with
  | .Mbool, .BR (.IR res) | .Mint8unsigned, .BR (.IR res) =>
    va (fun c r k => .Plbz res c r :: k) (fun r1 r2 k => .Plbzx res r1 r2 :: k) true addr .GPR11
  | .Mint8signed, .BR (.IR res) =>
    va (fun c r k => .Plbz res c r :: .Pextsb res res :: k)
      (fun r1 r2 k => .Plbzx res r1 r2 :: .Pextsb res res :: k) true addr .GPR11
  | .Mint16unsigned, .BR (.IR res) =>
    va (fun c r k => .Plhz res c r :: k) (fun r1 r2 k => .Plhzx res r1 r2 :: k) true addr .GPR11
  | .Mint16signed, .BR (.IR res) =>
    va (fun c r k => .Plha res c r :: k) (fun r1 r2 k => .Plhax res r1 r2 :: k) true addr .GPR11
  | .Mint32, .BR (.IR res) | .Many32, .BR (.IR res) =>
    va (fun c r k => .Plwz res c r :: k) (fun r1 r2 k => .Plwzx res r1 r2 :: k) true addr .GPR11
  | .Mfloat32, .BR (.FR res) =>
    va (fun c r k => .Plfs res c r :: k) (fun r1 r2 k => .Plfsx res r1 r2 :: k) true addr .GPR11
  | .Mfloat64, .BR (.FR res) | .Many64, .BR (.FR res) =>
    va (fun c r k => .Plfd res c r :: k) (fun r1 r2 k => .Plfdx res r1 r2 :: k) true addr .GPR11
  | .Mint64, .BR (.IR res) | .Many64, .BR (.IR res) =>
    va (fun c r k => .Pld res c r :: k) (fun r1 r2 k => .Pldx res r1 r2 :: k) false addr .GPR11
  | .Mint64, .BR_splitlong (.BR (.IR hi)) (.BR (.IR lo)) =>
    va (fun c r k =>
          match offsetConstant c (I 4) with
          | some c' => expandLoadInt64 hi lo r c c' k
          | none => .Paddi .GPR11 r c :: expandLoadInt64 hi lo .GPR11 (.Cint 0) (.Cint (I 4)) k)
      (fun r1 r2 k => .Padd .GPR11 r1 r2 :: expandLoadInt64 hi lo .GPR11 (.Cint 0) (.Cint (I 4)) k)
      true addr .GPR11
  | _, _ => err "expand_builtin_vload_1"

/-- `Asmexpand.expand_builtin_vload` -/
def expandBuiltinVload (o : Options) (chunk : Chunk) (args : List (BuiltinArg Preg))
    (res : BuiltinRes Preg) : PM Unit :=
  match args with
  | [addr] => expandBuiltinVload1 o chunk addr res
  | _ => err "expand_builtin_vload"

/-- `Asmexpand.temp_for_vstore` -/
def tempForVstore (src : BuiltinArg Preg) : Ireg :=
  let rl := src.params
  if !rl.contains (.IR .GPR11) then .GPR11
  else if !rl.contains (.IR .GPR12) then .GPR12
  else .GPR10

/-- `Asmexpand.expand_store_int64` -/
def expandStoreInt64 (hi lo base : Ireg) (ofsHi ofsLo : Constant) (k : Code) : Code :=
  .Pstw hi ofsHi base :: .Pstw lo ofsLo base :: k

/-- `Asmexpand.expand_builtin_vstore_1` -/
def expandBuiltinVstore1 (o : Options) (chunk : Chunk) (addr src : BuiltinArg Preg) : PM Unit :=
  let temp := tempForVstore src
  let va := expandVolatileAccess o
  match chunk, src with
  | .Mbool, .BA (.IR src) | .Mint8signed, .BA (.IR src) | .Mint8unsigned, .BA (.IR src) =>
    va (fun c r k => .Pstb src c r :: k) (fun r1 r2 k => .Pstbx src r1 r2 :: k) true addr temp
  | .Mint16signed, .BA (.IR src) | .Mint16unsigned, .BA (.IR src) =>
    va (fun c r k => .Psth src c r :: k) (fun r1 r2 k => .Psthx src r1 r2 :: k) true addr temp
  | .Mint32, .BA (.IR src) | .Many32, .BA (.IR src) =>
    va (fun c r k => .Pstw src c r :: k) (fun r1 r2 k => .Pstwx src r1 r2 :: k) true addr temp
  | .Mfloat32, .BA (.FR src) =>
    va (fun c r k => .Pstfs src c r :: k) (fun r1 r2 k => .Pstfsx src r1 r2 :: k) true addr temp
  | .Mfloat64, .BA (.FR src) | .Many64, .BA (.FR src) =>
    va (fun c r k => .Pstfd src c r :: k) (fun r1 r2 k => .Pstfdx src r1 r2 :: k) true addr temp
  | .Mint64, .BA (.IR src) | .Many64, .BA (.IR src) =>
    va (fun c r k => .Pstd src c r :: k) (fun r1 r2 k => .Pstdx src r1 r2 :: k) false addr temp
  | .Mint64, .BA_splitlong (.BA (.IR hi)) (.BA (.IR lo)) =>
    va (fun c r k =>
          match offsetConstant c (I 4) with
          | some c' => expandStoreInt64 hi lo r c c' k
          | none => .Paddi temp r c :: expandStoreInt64 hi lo temp (.Cint 0) (.Cint (I 4)) k)
      (fun r1 r2 k => .Padd temp r1 r2 :: expandStoreInt64 hi lo temp (.Cint 0) (.Cint (I 4)) k)
      true addr temp
  | _, _ => err "expand_builtin_vstore_1"

/-- `Asmexpand.expand_builtin_vstore` -/
def expandBuiltinVstore (o : Options) (chunk : Chunk) (args : List (BuiltinArg Preg)) : PM Unit :=
  match args with
  | [addr, src] => expandBuiltinVstore1 o chunk addr src
  | _ => err "expand_builtin_vstore"

/-! ## Variable arguments -/

/-- `Asmexpand.align` (for `a` a power of 2 and `n ≥ 0`) -/
def align (n a : Int) : Int := (n + a - 1) / a * a

/-- `Asmexpand.next_arg_locations` -/
def nextArgLocations (ir fr ofs : Int) : List ATyp → Int × Int × Int
  | [] => (ir, fr, ofs)
  | ty :: l =>
    match ty with
    | .Tint | .Tany32 =>
      if ir < 8 then nextArgLocations (ir + 1) fr ofs l else nextArgLocations ir fr (ofs + 4) l
    | .Tfloat | .Tsingle | .Tany64 =>
      if fr < 8 then nextArgLocations ir (fr + 1) ofs l
      else nextArgLocations ir fr (align ofs 8 + 8) l
    | .Tlong =>
      let ir := align ir 2
      if ir < 8 then nextArgLocations (ir + 2) fr ofs l
      else nextArgLocations ir fr (align ofs 8 + 8) l

/-- `Asmexpand.expand_builtin_va_start` -/
def expandBuiltinVaStart (r : Ireg) : PM Unit := do
  if !(← (isCurrentFunctionVariadic : EM Bool)) then
    err "Fatal error: va_start used in non-vararg function"
  let (ir, fr, ofs) := nextArgLocations 0 0 0 (← (getCurrentFunctionArgs : EM (List ATyp)))
  let cs := (← (get : EM _)).stacksize
  emitLoadimm .GPR0 (I ir)
  em (.Pstb .GPR0 (.Cint 0) r)
  emitLoadimm .GPR0 (I fr)
  em (.Pstb .GPR0 (.Cint (I 1)) r)
  emitAddimm .GPR0 .GPR1 (I (cs + 8 + ofs))
  em (.Pstw .GPR0 (.Cint (I 4)) r)
  emitAddimm .GPR0 .GPR1 (I (cs - 96))
  em (.Pstw .GPR0 (.Cint (I 8)) r)

/-- `Asmexpand.expand_int64_arith`: go through `GPR0` when the low word
    would overwrite an argument still needed. -/
def expandInt64Arith (conflict : Bool) (rl : Ireg) (fn : Ireg → PM Unit) : PM Unit :=
  if conflict then do fn .GPR0; em (.Pmr rl .GPR0) else fn rl

/-! ## Conditional moves -/

/-- `Asmexpand.expand_integer_cond_move_1` (`GPR0` is all ones if the
    condition is true, 0 otherwise) -/
def expandIntegerCondMove1 (a2 a3 res : Ireg) : PM Unit := do
  if res ≠ a3 then
    em (.Pand_ res a2 .GPR0)
    em (.Pandc .GPR0 a3 .GPR0)
  else
    em (.Pandc res a3 .GPR0)
    em (.Pand_ .GPR0 a2 .GPR0)
  em (.Por res res .GPR0)

/-- `Asmexpand.expand_integer_cond_move` -/
def expandIntegerCondMove (o : Options) (a1 a2 a3 res : Ireg) : PM Unit :=
  if a2 == a3 then em (.Pmr res a2)
  else if o.eref then do
    em (.Pcmpwi a1 (.Cint 0))
    em (.Pisel res a3 a2 .CRbit_2)
  else do
    -- a1 has type _Bool, hence it is 0 or 1
    em (.Psubfic .GPR0 a1 (.Cint 0))
    expandIntegerCondMove1 a2 a3 res

/-- `Asmexpand.expand_float_cond_move` -/
def expandFloatCondMove (bit : Crbit) (a2 a3 res : Freg) : PM Unit := do
  em (.Pmfcr .GPR0)
  em (.Prlwinm .GPR0 .GPR0 (I (4 + numCrbit bit)) (I 8))
  em (.Pstfdu a3 (.Cint (I (-16))) .GPR1)
  em (.Pcfi_adjust (I 16))
  em (.Pstfd a2 (.Cint (I 8)) .GPR1)
  em (.Plfdx res .GPR1 .GPR0)
  em (.Paddi .GPR1 .GPR1 (.Cint (I 16)))
  em (.Pcfi_adjust (I (-16)))

/-- `Asmexpand.expand_isel`: emulate `isel` on processors without it. -/
def expandIsel (o : Options) (bit : Crbit) (a2 a3 res : Ireg) : PM Unit :=
  if a2 == a3 then em (.Pmr res a2)
  else if o.eref then em (.Pisel res a2 a3 bit)
  else do
    em (.Pmfcr .GPR0)
    em (.Prlwinm .GPR0 .GPR0 (I (1 + numCrbit bit)) (I 1))
    em (.Psubfic .GPR0 .GPR0 (.Cint 0))
    expandIntegerCondMove1 a2 a3 res

/-- `Asmexpand.int_to_int_reg` -/
def intToIntReg (n : Int) : Option Ireg :=
  [Ireg.GPR0, .GPR1, .GPR2, .GPR3, .GPR4, .GPR5, .GPR6, .GPR7, .GPR8, .GPR9, .GPR10, .GPR11,
   .GPR12, .GPR13, .GPR14, .GPR15, .GPR16, .GPR17, .GPR18, .GPR19, .GPR20, .GPR21, .GPR22,
   .GPR23, .GPR24, .GPR25, .GPR26, .GPR27, .GPR28, .GPR29, .GPR30, .GPR31][n.toNat]?
    |>.filter (fun _ => n ≥ 0)

/-! ## Built-ins inlined by the compiler -/

/-- `Asmexpand.expand_builtin_inline` (temporaries: `GPR0`, `FPR13`) -/
def expandBuiltinInline (o : Options) (name : String) (args : List (BuiltinArg Preg))
    (res : BuiltinRes Preg) : PM Unit :=
  let only64 := fun (k : PM Unit) =>
    if o.ppc64 then k else err s!"{name} is only supported for PPC64 targets"
  match name, args, res with
  -- Integer arithmetic
  | "__builtin_mulhw", [.BA (.IR a1), .BA (.IR a2)], .BR (.IR res) => em (.Pmulhw res a1 a2)
  | "__builtin_mulhwu", [.BA (.IR a1), .BA (.IR a2)], .BR (.IR res) => em (.Pmulhwu res a1 a2)
  | "__builtin_mulhd", [.BA (.IR a1), .BA (.IR a2)], .BR (.IR res) => only64 (em (.Pmulhd res a1 a2))
  | "__builtin_mulhdu", [.BA (.IR a1), .BA (.IR a2)], .BR (.IR res) =>
    only64 (em (.Pmulhdu res a1 a2))
  | "__builtin_clz", [.BA (.IR a1)], .BR (.IR res)
  | "__builtin_clzl", [.BA (.IR a1)], .BR (.IR res) => em (.Pcntlzw res a1)
  | "__builtin_clzll", [.BA (.IR a1)], .BR (.IR res) => em (.Pcntlzd res a1)
  | "__builtin_clzll", [.BA_splitlong (.BA (.IR ah)) (.BA (.IR al))], .BR (.IR res) => do
    let lbl ← newLbl
    em (.Pcntlzw .GPR0 al)
    em (.Pcntlzw res ah)
    -- less than 32 bits zero?
    em (.Pcmpwi res (.Cint (I 32)))
    em (.Pbf .CRbit_2 lbl)
    -- high bits all zero, count bits in low word and increment by 32
    em (.Padd res res .GPR0)
    em (.Plabel lbl)
  | "__builtin_ctz", [.BA (.IR a1)], .BR (.IR res)
  | "__builtin_ctzl", [.BA (.IR a1)], .BR (.IR res) => do
    em (.Paddi .GPR0 a1 (.Cint (I (-1))))   -- tmp := x-1
    em (.Pandc res .GPR0 a1)                -- res := tmp & ~(x)
    em (.Pcntlzw res res)                   -- res := #leading zeros
    em (.Psubfic res res (.Cint (I 32)))    -- res := 32 - #leading zeros
  | "__builtin_ctzll", [.BA (.IR a1)], .BR (.IR res) => do
    em (.Paddi64 .GPR0 a1 (L (-1)))
    em (.Pandc res .GPR0 a1)
    em (.Pcntlzd res res)
    em (.Psubfic64 res res (L 64))
  | "__builtin_ctzll", [.BA_splitlong (.BA (.IR ah)) (.BA (.IR al))], .BR (.IR res) => do
    let lbl1 ← newLbl
    let lbl2 ← newLbl
    -- low word equal to zero?
    em (.Pcmpwi al (.Cint 0))
    em (.Pbf .CRbit_2 lbl1)
    -- low word is zero, count trailing zeros in high word and increment by 32
    em (.Paddi .GPR0 ah (.Cint (I (-1))))
    em (.Pandc res .GPR0 ah)
    em (.Pcntlzw res res)
    em (.Psubfic res res (.Cint (I 64)))
    em (.Pb lbl2)
    -- count trailing zeros in low word
    em (.Plabel lbl1)
    em (.Paddi .GPR0 al (.Cint (I (-1))))
    em (.Pandc res .GPR0 al)
    em (.Pcntlzw res res)
    em (.Psubfic res res (.Cint (I 32)))
    em (.Plabel lbl2)
  | "__builtin_cmpb", [.BA (.IR a1), .BA (.IR a2)], .BR (.IR res) => em (.Pcmpb res a1 a2)
  | "__builtin_bswap64", [.BA_splitlong (.BA (.IR ah)) (.BA (.IR al))],
      .BR_splitlong (.BR (.IR rh)) (.BR (.IR rl)) => do
    if o.ppc64 then err "__builtin_bswap64: unexpected register pair on PPC64"
    em (.Pstwu ah (.Cint (I (-8))) .GPR1)
    em (.Pcfi_adjust (I 8))
    em (.Pstwu al (.Cint (I (-8))) .GPR1)
    em (.Pcfi_adjust (I 8))
    em (.Plwbrx rh .GPR0 .GPR1)
    em (.Paddi .GPR1 .GPR1 (.Cint (I 8)))
    em (.Pcfi_adjust (I (-8)))
    em (.Plwbrx rl .GPR0 .GPR1)
    em (.Paddi .GPR1 .GPR1 (.Cint (I 8)))
    em (.Pcfi_adjust (I (-8)))
  | "__builtin_bswap64", [.BA (.IR a1)], .BR (.IR res) => do
    if !o.ppc64 then err "__builtin_bswap64: 64-bit register on a 32-bit target"
    em (.Pstdu a1 (.Cint (I (-8))) .GPR1)
    em (.Pcfi_adjust (I 8))
    em (.Pldbrx res .GPR0 .GPR1)
    em (.Paddi .GPR1 .GPR1 (.Cint (I 8)))
    em (.Pcfi_adjust (I (-8)))
  | "__builtin_bswap", [.BA (.IR a1)], .BR (.IR res)
  | "__builtin_bswap32", [.BA (.IR a1)], .BR (.IR res) => do
    em (.Pstwu a1 (.Cint (I (-8))) .GPR1)
    em (.Pcfi_adjust (I 8))
    em (.Plwbrx res .GPR0 .GPR1)
    em (.Paddi .GPR1 .GPR1 (.Cint (I 8)))
    em (.Pcfi_adjust (I (-8)))
  | "__builtin_bswap16", [.BA (.IR a1)], .BR (.IR res) => do
    em (.Prlwinm .GPR0 a1 (I 8) (I 0x0000FF00))
    em (.Prlwinm res a1 (I 24) (I 0x000000FF))
    em (.Por res .GPR0 res)
  -- Float arithmetic
  | "__builtin_fmadd", [.BA (.FR a1), .BA (.FR a2), .BA (.FR a3)], .BR (.FR res) =>
    em (.Pfmadd res a1 a2 a3)
  | "__builtin_fmsub", [.BA (.FR a1), .BA (.FR a2), .BA (.FR a3)], .BR (.FR res) =>
    em (.Pfmsub res a1 a2 a3)
  | "__builtin_fnmadd", [.BA (.FR a1), .BA (.FR a2), .BA (.FR a3)], .BR (.FR res) =>
    em (.Pfnmadd res a1 a2 a3)
  | "__builtin_fnmsub", [.BA (.FR a1), .BA (.FR a2), .BA (.FR a3)], .BR (.FR res) =>
    em (.Pfnmsub res a1 a2 a3)
  | "__builtin_fsqrt", [.BA (.FR a1)], .BR (.FR res)
  | "__builtin_sqrt", [.BA (.FR a1)], .BR (.FR res) => em (.Pfsqrt res a1)
  | "__builtin_frsqrte", [.BA (.FR a1)], .BR (.FR res) => em (.Pfrsqrte res a1)
  | "__builtin_fres", [.BA (.FR a1)], .BR (.FR res) => em (.Pfres res a1)
  | "__builtin_fsel", [.BA (.FR a1), .BA (.FR a2), .BA (.FR a3)], .BR (.FR res) =>
    em (.Pfsel res a1 a2 a3)
  | "__builtin_fcti", [.BA (.FR a1)], .BR (.IR res) => do
    em (.Pfctiw .FPR13 a1)
    em (.Pstfdu .FPR13 (.Cint (I (-8))) .GPR1)
    em (.Pcfi_adjust (I 8))
    em (.Plwz res (.Cint (I 4)) .GPR1)
    em (.Paddi .GPR1 .GPR1 (.Cint (I 8)))
    em (.Pcfi_adjust (I (-8)))
  -- 64-bit integer arithmetic
  | "__builtin_negl", [.BA_splitlong (.BA (.IR ah)) (.BA (.IR al))],
      .BR_splitlong (.BR (.IR rh)) (.BR (.IR rl)) =>
    expandInt64Arith (rl == ah) rl fun rl => do
      em (.Psubfic rl al (.Cint 0))
      em (.Psubfze rh ah)
  | "__builtin_addl", [.BA_splitlong (.BA (.IR ah)) (.BA (.IR al)),
                       .BA_splitlong (.BA (.IR bh)) (.BA (.IR bl))],
      .BR_splitlong (.BR (.IR rh)) (.BR (.IR rl)) =>
    expandInt64Arith (rl == ah || rl == bh) rl fun rl => do
      em (.Paddc rl al bl)
      em (.Padde rh ah bh)
  | "__builtin_subl", [.BA_splitlong (.BA (.IR ah)) (.BA (.IR al)),
                       .BA_splitlong (.BA (.IR bh)) (.BA (.IR bl))],
      .BR_splitlong (.BR (.IR rh)) (.BR (.IR rl)) =>
    expandInt64Arith (rl == ah || rl == bh) rl fun rl => do
      em (.Psubfc rl bl al)
      em (.Psubfe rh bh ah)
  | "__builtin_mull", [.BA (.IR a), .BA (.IR b)], .BR_splitlong (.BR (.IR rh)) (.BR (.IR rl)) =>
    expandInt64Arith (rl == a || rl == b) rl fun rl => do
      em (.Pmullw rl a b)
      em (.Pmulhwu rh a b)
  -- Memory accesses
  | "__builtin_read16_reversed", [.BA (.IR a1)], .BR (.IR res) => em (.Plhbrx res .GPR0 a1)
  | "__builtin_read32_reversed", [.BA (.IR a1)], .BR (.IR res) => em (.Plwbrx res .GPR0 a1)
  | "__builtin_read64_reversed", [.BA (.IR a1)], .BR (.IR res) =>
    if o.ppc64 then em (.Pldbrx res .GPR0 a1)
    else err "__builtin_read64_reversed is only supported for PPC64 targets"
  | "__builtin_write16_reversed", [.BA (.IR a1), .BA (.IR a2)], _ => em (.Psthbrx a2 .GPR0 a1)
  | "__builtin_write32_reversed", [.BA (.IR a1), .BA (.IR a2)], _ => em (.Pstwbrx a2 .GPR0 a1)
  | "__builtin_write64_reversed", [.BA (.IR a1), .BA (.IR a2)], _ =>
    if o.ppc64 then em (.Pstdbrx a2 .GPR0 a1)
    else err "__builtin_write64_reversed is only supported for PPC64 targets"
  -- Synchronization
  | "__builtin_membar", [], _ => pure ()
  | "__builtin_eieio", [], _ => em .Peieio
  | "__builtin_sync", [], _ => em .Psync
  | "__builtin_isync", [], _ => em .Pisync
  | "__builtin_lwsync", [], _ => em .Plwsync
  | "__builtin_mbar", [.BA_int mo], _ => do
    if !(mo == 0 || mo == 1) then err "the argument of __builtin_mbar must be 0 or 1"
    em (.Pmbar mo)
  | "__builtin_mbar", _, _ => err "the argument of __builtin_mbar must be a constant"
  | "__builtin_trap", [], _ => em .Ptrap
  -- Vararg stuff
  | "__builtin_va_start", [.BA (.IR a)], _ => expandBuiltinVaStart a
  -- Cache control
  | "__builtin_dcbf", [.BA (.IR a1)], _ => em (.Pdcbf .GPR0 a1)
  | "__builtin_dcbi", [.BA (.IR a1)], _ => em (.Pdcbi .GPR0 a1)
  | "__builtin_icbi", [.BA (.IR a1)], _ => em (.Picbi .GPR0 a1)
  | "__builtin_dcbtls", [.BA (.IR a1), .BA_int loc], _ => do
    if !(loc == 0 || loc == 2) then err "the second argument of __builtin_dcbtls must be 0 or 2"
    em (.Pdcbtls loc .GPR0 a1)
  | "__builtin_dcbtls", _, _ => err "the second argument of __builtin_dcbtls must be a constant"
  | "__builtin_icbtls", [.BA (.IR a1), .BA_int loc], _ => do
    if !(loc == 0 || loc == 2) then err "the second argument of __builtin_icbtls must be 0 or 2"
    em (.Picbtls loc .GPR0 a1)
  | "__builtin_icbtls", _, _ => err "the second argument of __builtin_icbtls must be a constant"
  | "__builtin_prefetch", [.BA (.IR a1), .BA_int rw, .BA_int loc], _ => do
    if !(Integers.Int.ltu loc (I 4)) then
      err "the last argument of __builtin_prefetch must be 0, 1 or 2"
    if rw == 0 then em (.Pdcbt loc .GPR0 a1)
    else if rw == 1 then em (.Pdcbtst loc .GPR0 a1)
    else err "the second argument of __builtin_prefetch must be 0 or 1"
  | "__builtin_prefetch", _, _ =>
    err "the second and third argument of __builtin_prefetch must be a constant"
  | "__builtin_dcbz", [.BA (.IR a1)], _ => em (.Pdcbz .GPR0 a1)
  -- Special registers
  | "__builtin_get_spr", [.BA_int n], .BR (.IR res) => em (.Pmfspr res n)
  | "__builtin_get_spr", _, _ => err "the argument of __builtin_get_spr must be a constant"
  | "__builtin_set_spr", [.BA_int n, .BA (.IR a1)], _ => em (.Pmtspr n a1)
  | "__builtin_set_spr", _, _ => err "the first argument of __builtin_set_spr must be a constant"
  -- Special registers in 32-bit hybrid mode
  | "__builtin_get_spr64", [.BA_int n], .BR (.IR r) => only64 (em (.Pmfspr r n))
  | "__builtin_get_spr64", _, _ =>
    only64 (err "the argument of __builtin_get_spr64 must be a constant")
  | "__builtin_set_spr64", [.BA_int n, .BA (.IR a)], _ => only64 (em (.Pmtspr n a))
  | "__builtin_set_spr64", _, _ =>
    only64 (err "the first argument of __builtin_set_spr64 must be a constant")
  -- Move registers
  | "__builtin_mr", [.BA_int dst, .BA_int src], _ =>
    match intToIntReg (Integers.Int.unsigned dst), intToIntReg (Integers.Int.unsigned src) with
    | some dst, some src => em (.Pori dst src (.Cint 0))
    | _, _ => err "the arguments of __builtin_mr must be in the range of 0..31"
  | "__builtin_mr", _, _ => err "the arguments of __builtin_mr must be constants"
  -- Frame and return address
  | "__builtin_call_frame", _, .BR (.IR res) => do
    let sz := (← (get : EM _)).stacksize
    if sz < 0x8000 && sz ≥ 0 then em (.Paddi res .GPR1 (.Cint (I sz)))
    else em (.Plwz res (.Cint (← get).linkOfs) .GPR1)
  | "__builtin_return_address", _, .BR (.IR res) => do
    em (.Plwz res (.Cint (← get).retOfs) .GPR1)
  -- Integer selection
  | "__builtin_bsel", [.BA (.IR a1), .BA (.IR a2), .BA (.IR a3)], .BR (.IR res)
  | "__builtin_isel", [.BA (.IR a1), .BA (.IR a2), .BA (.IR a3)], .BR (.IR res)
  | "__builtin_uisel", [.BA (.IR a1), .BA (.IR a2), .BA (.IR a3)], .BR (.IR res) =>
    expandIntegerCondMove o a1 a2 a3 res
  | "__builtin_isel64", [.BA (.IR a1), .BA (.IR a2), .BA (.IR a3)], .BR (.IR res)
  | "__builtin_uisel64", [.BA (.IR a1), .BA (.IR a2), .BA (.IR a3)], .BR (.IR res) =>
    only64 (expandIntegerCondMove o a1 a2 a3 res)
  -- No operation
  | "__builtin_nop", [], _ => em (.Pori .GPR0 .GPR0 (.Cint 0))
  -- Optimization hint
  | "__builtin_unreachable", [], _ => pure ()
  -- Atomic operations
  | "__builtin_atomic_exchange", [.BA (.IR a1), .BA (.IR a2), .BA (.IR a3)], _ => do
    -- Register constraints imposed by Machregs.v
    if !(a1 == .GPR3 && a2 == .GPR4 && a3 == .GPR5) then err "__builtin_atomic_exchange: registers"
    em (.Plwz .GPR10 (.Cint 0) a2)
    em .Psync
    let lbl ← newLbl
    em (.Plabel lbl)
    em (.Plwarx .GPR0 .GPR0 a1)
    em (.Pstwcx_ .GPR10 .GPR0 a1)
    em (.Pbf .CRbit_2 lbl)
    em .Pisync
    em (.Pstw .GPR0 (.Cint 0) a3)
  | "__builtin_atomic_load", [.BA (.IR a1), .BA (.IR a2)], _ => do
    let lbl ← newLbl
    em .Psync
    em (.Plwz .GPR0 (.Cint 0) a1)
    em (.Pcmpw .GPR0 .GPR0)
    em (.Pbf .CRbit_2 lbl)
    em (.Plabel lbl)
    em .Pisync
    em (.Pstw .GPR0 (.Cint 0) a2)
  | "__builtin_sync_fetch_and_add", [.BA (.IR a1), .BA (.IR a2)], .BR (.IR res) => do
    if !(a1 == .GPR4 && a2 == .GPR5 && res == .GPR3) then
      err "__builtin_sync_fetch_and_add: registers"
    let lbl ← newLbl
    em .Psync
    em (.Plabel lbl)
    em (.Plwarx res .GPR0 a1)
    em (.Padd .GPR0 res a2)
    em (.Pstwcx_ .GPR0 .GPR0 a1)
    em (.Pbf .CRbit_2 lbl)
    em .Pisync
  | "__builtin_atomic_compare_exchange", [.BA (.IR dst), .BA (.IR exp), .BA (.IR des)],
      .BR (.IR res) => do
    if !(dst == .GPR4 && exp == .GPR5 && des == .GPR6 && res == .GPR3) then
      err "__builtin_atomic_compare_exchange: registers"
    let lbls ← newLbl
    let lblneq ← newLbl
    let lblsucc ← newLbl
    em (.Plwz .GPR10 (.Cint 0) exp)
    em (.Plwz .GPR11 (.Cint 0) des)
    em .Psync
    em (.Plabel lbls)
    em (.Plwarx .GPR0 .GPR0 dst)
    em (.Pcmpw .GPR0 .GPR10)
    em (.Pbf .CRbit_2 lblneq)
    em (.Pstwcx_ .GPR11 .GPR0 dst)
    em (.Pbf .CRbit_2 lbls)
    em (.Plabel lblneq)
    -- Here, CR2 is true if the exchange succeeded, false if it failed
    em .Pisync
    em (.Pmfcr .GPR10)
    em (.Prlwinm res .GPR10 (I 3) (I 1))
    -- Update exp with the current value of dst if the exchange failed
    em (.Pbt .CRbit_2 lblsucc)
    em (.Pstw .GPR0 (.Cint 0) exp)
    em (.Plabel lblsucc)
  -- Catch-all
  | _, _, _ => err ("unrecognized builtin " ++ name)

/-- `Asmexpand.set_cr6`: before a call to a variadic or unprototyped
    function, condition bit 6 is set iff at least one argument is a float. -/
def setCr6 (sg : Signature) : PM Unit :=
  if sg.sig_cc.cc_vararg.isSome || sg.sig_cc.cc_unproto then
    if sg.sig_args.any (fun | .Xfloat | .Xsingle => true | _ => false) then
      em (.Pcreqv .CRbit_6 .CRbit_6 .CRbit_6)
    else em (.Pcrxor .CRbit_6 .CRbit_6 .CRbit_6)
  else pure ()

/-! ## Branch relaxation -/

/-- `Asmexpand.num_statements_inline_asm`: an upper bound on the number of
    instructions of a piece of inline assembly (comments and blank lines
    removed, then split at newlines and `;`). -/
def numStatementsInlineAsm (diab : Bool) (txt : String) : Nat :=
  -- `Str.global_replace re_asm_comment ""`
  let isComment := fun (c : Char) => c == '#' || (diab && c == ';')
  let lines := (txt.splitOn "\n").map fun l =>
    String.ofList (l.toList.takeWhile (fun c => !isComment c))
  -- `Str.global_replace re_blank_line ""`: a blank line followed by a newline
  let n := lines.length
  let lines := (lines.zipIdx).filterMap fun (l, i) =>
    if i + 1 < n && l.toList.all (fun c => c == ' ' || c == '\t') then none else some (l, i)
  let txt := "\n".intercalate (lines.map (·.1))
  let txt := if lines.getLast?.map (·.2) == some (n - 1) || lines.isEmpty then txt else txt ++ "\n"
  -- `Str.split re_asm_stmt_separator`
  let cs := txt.toList
  let isSep := fun (c : Char) => c == '\n' || c == ';'
  let cs := match cs with
    | c :: rest => if isSep c then rest else cs
    | [] => []
  let rec go (fuel : Nat) (cs : List Char) (acc : Nat) : Nat :=
    match fuel with
    | 0 => acc
    | fuel + 1 =>
      if cs.isEmpty then acc
      else
        let tok := cs.takeWhile (fun c => !isSep c)
        let rest := cs.drop tok.length
        match rest with
        | [] => acc + 1
        | _ :: rest => go fuel rest (acc + 1)
  go (cs.length + 1) cs 0

#guard numStatementsInlineAsm false "mr %0, %1 # comment\n\n  \nnop; nop" = 3

/-- `BInfo.builtin_size` -/
def builtinSize (diab : Bool) : ExtFun → Except String Int
  | .EF_annot _ _ _ => .ok 0
  | .EF_debug _ _ _ => .ok 0
  | .EF_inline_asm txt _ _ => .ok (4 * numStatementsInlineAsm diab txt)
  | _ => .error "builtin_size"

/-- `BInfo.instr_size` -/
def instrSize (diab : Bool) : Instruction → Nat
  | .Pbtbl _ _ => 20
  | .Pldi _ _ => 8
  | .Plfi _ _ => 8
  | .Plfis _ _ => 8
  | .Plabel _ => 0
  | .Pbuiltin ef _ _ => match builtinSize diab ef with | .ok n => n.toNat | .error _ => 0
  | .Pcfi_adjust _ | .Pcfi_rel_offset _ => 0
  | _ => 4

/-- `BInfo.need_relaxation` -/
def needRelaxation (map : Positive → Except String Int) (pc : Int) : Instruction → Except String Bool
  | .Pbf _ lbl | .Pbt _ lbl => do
    let displ := (← map lbl) - pc
    return displ < -0x8000 || displ ≥ 0x8000
  | _ => .ok false

/-- `BInfo.relax_instruction` -/
def relaxInstruction : Instruction → EM (List Instruction)
  | .Pbf bit lbl => do let l ← newLabel; return [.Pbt bit l, .Pb lbl, .Plabel l]
  | .Pbt bit lbl => do let l ← newLabel; return [.Pbf bit l, .Pb lbl, .Plabel l]
  | _ => error "relax_instruction"

/-- `Asmexpand.BInfo` -/
def bInfo (diab : Bool) : BranchInformation Instruction where
  instrSize := instrSize diab
  needRelaxation := needRelaxation
  relaxInstruction := relaxInstruction

/-! ## Expansion of instructions -/

/-- `Asmexpand.expand_instruction` -/
def expandInstruction (o : Options) (instr : Instruction) : PM Unit :=
  match instr with
  | .Pallocframe sz ofs retofs => do
    let variadic ← (isCurrentFunctionVariadic : EM Bool)
    if ofsInt ofs ≠ 0 then err "Pallocframe: nonzero offset of the back link"
    let sz := if variadic then sz + 96 else sz
    let adj := -sz
    if adj ≥ -0x8000 && adj < 0 then
      em (.Pstwu .GPR1 (.Cint (I adj)) .GPR1)
    else
      emitLoadimm .GPR0 (I adj)
      em (.Pstwux .GPR1 .GPR1 .GPR0)
    em (.Pcfi_adjust (I sz))
    if variadic then
      em (.Pmflr .GPR0)
      em (.Pbl o.vaSaveregs { sig_args := [], sig_res := .Xvoid, sig_cc := cc_default })
      em (.Pmtlr .GPR0)
    (modify fun s => { s with stacksize := sz } : EM Unit)
    modify fun s => { s with linkOfs := ofsInt ofs, retOfs := ofsInt retofs }
  | .Pbctr sg | .Pbctrl sg | .Pbl _ sg | .Pbs _ sg => do
    setCr6 sg
    em instr
  | .Pextzw r1 r2 => em (.Prldinm r1 r2 (I 0) lower32)
  | .Pfreeframe sz ofs => do
    let variadic ← (isCurrentFunctionVariadic : EM Bool)
    let sz := if variadic then sz + 96 else sz
    if sz < 0x8000 && sz ≥ 0 then em (.Paddi .GPR1 .GPR1 (.Cint (I sz)))
    else em (.Plwz .GPR1 (.Cint (ofsInt ofs)) .GPR1)
  | .Pfcfl r1 r2 => do
    if !o.ppc64 then err "Pfcfl is only supported for PPC64 targets"
    em (.Pstdu r2 (.Cint (I (-8))) .GPR1)
    em (.Pcfi_adjust (I 8))
    em (.Plfd r1 (.Cint 0) .GPR1)
    em (.Pfcfid r1 r1)
    em (.Paddi .GPR1 .GPR1 (.Cint (I 8)))
    em (.Pcfi_adjust (I (-8)))
  | .Pfcti r1 r2 => do
    em (.Pfctiwz .FPR13 r2)
    em (.Pstfdu .FPR13 (.Cint (I (-8))) .GPR1)
    em (.Pcfi_adjust (I 8))
    em (.Plwz r1 (.Cint (I 4)) .GPR1)
    em (.Paddi .GPR1 .GPR1 (.Cint (I 8)))
    em (.Pcfi_adjust (I (-8)))
  | .Pfctid r1 r2 => do
    if !o.ppc64 then err "Pfctid is only supported for PPC64 targets"
    em (.Pfctidz .FPR13 r2)
    em (.Pstfdu .FPR13 (.Cint (I (-8))) .GPR1)
    em (.Pcfi_adjust (I 8))
    em (.Pld r1 (.Cint 0) .GPR1)
    em (.Paddi .GPR1 .GPR1 (.Cint (I 8)))
    em (.Pcfi_adjust (I (-8)))
  | .Pfmake rd r1 r2 => do
    em (.Pstwu r1 (.Cint (I (-8))) .GPR1)
    em (.Pcfi_adjust (I 8))
    em (.Pstw r2 (.Cint (I 4)) .GPR1)
    em (.Plfd rd (.Cint 0) .GPR1)
    em (.Paddi .GPR1 .GPR1 (.Cint (I 8)))
    em (.Pcfi_adjust (I (-8)))
  | .Pfxdp r1 r2 => if r1 ≠ r2 then em (.Pfmr r1 r2) else pure ()
  | .Pisel rd r1 r2 bit => expandIsel o bit r1 r2 rd
  | .Pfsel_gen rd r1 r2 bit => expandFloatCondMove bit r1 r2 rd
  | .Plmake r1 rhi rlo =>
    if r1 == rlo then em (.Prldimi r1 rhi (I 32) upper32)
    else if r1 == rhi then do
      em (.Prldinm r1 rhi (I 32) upper32)
      em (.Prldimi r1 rlo (I 0) lower32)
    else do
      em (.Pmr r1 rlo)
      em (.Prldimi r1 rhi (I 32) upper32)
  | .Pllo _ => pure ()   -- no computational content
  | .Plhi r1 r2 => em (.Prldinm r1 r2 (I 32) lower32)
  | .Pmfcrbit r1 bit => do
    em (.Pmfcr r1)
    em (.Prlwinm r1 r1 (I (1 + numCrbit bit)) (I 1))
  | .Pbuiltin ef args res =>
    match ef with
    | .EF_builtin name _ => expandBuiltinInline o name args res
    | .EF_vload chunk => expandBuiltinVload o chunk args res
    | .EF_vstore chunk => expandBuiltinVstore o chunk args
    | .EF_memcpy sz al => expandBuiltinMemcpy o sz al args
    | .EF_annot_val kind txt targ => expandAnnotVal kind txt targ args res
    | .EF_annot _ _ _ | .EF_debug _ _ _ | .EF_inline_asm _ _ _ => em instr
    | _ => err "expand_instruction: unexpected builtin"
  | _ => em instr

/-- `Asmexpandaux.expand` (without `-g`), in the monad `PM`. -/
def expandCode (o : Options) : List Instruction → PM Unit
  | [] => pure ()
  | i :: rest => do
    expandInstruction o i
    match AsmInstr.annotKind i with
    | some kind => if kind.toNat = 2 && lblFollows rest then expandInstruction o builtinNop
    | none => pure ()
    expandCode o rest

/-- `Asmexpand.expand_function`: expansion, then branch relaxation. -/
def expandFunction (o : Options) (fn : Asm.Function) : Res Asm.Function :=
  let run : EM (List Instruction) := do
    setCurrentFunction fn.fn_sig fn.fn_code
    (expandCode o fn.fn_code).run' {}
    BranchRelaxation.relaxation (bInfo o.diab) (← getCurrentFunction)
  match run.run' {} with
  | .ok c => .OK { fn with fn_code := c }
  | .error s => .Error s

/-- `Asmexpand.expand_fundef` -/
def expandFundef (o : Options) : Asm.Fundef → Res Asm.Fundef
  | .Internal f =>
    match expandFunction o f with
    | .OK tf => .OK (.Internal tf)
    | .Error msg => .Error msg
  | .External ef => .OK (.External ef)

/-- `Asmexpand.expand_program` -/
def expandProgram (o : Options) (p : Asm.Program) : Res Asm.Program :=
  transformPartialProgram2 (fun _ f => expandFundef o f) (fun _ v => .OK v) p

end Asmexpand
end PowerPC
end CC
