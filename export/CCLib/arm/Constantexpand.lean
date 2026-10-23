/-
  Emission of literal pools for ARM — port of `arm/Constantexpand.ml`.

  After `Asmexpand`, the pseudo-instructions `Pflid`, `Pflis` and
  `Ploadsymbol` are replaced by loads from a literal pool (`Pflid_lbl`,
  `Pflis_lbl`, `Ploadsymbol_lbl`) or by immediate forms (`Pflid_imm`,
  `Pflis_imm`, `Ploadsymbol_imm`), and the pools (`Pconstants`) are emitted
  in the code, close enough to the instructions that use them (1 KiB for
  floats, 4 KiB for symbols).  Like the OCaml code, it is not verified.

  Differences from OCaml:
  * The global references (`currpos`, `size_constants`,
    `max_pos_constants`) and the three hash tables of labels are the fields
    of `Constantexpand.State`, threaded by the monad `CM` on top of the
    expansion monad `Asmexpandaux.M`.
  * The configuration (`Configuration.model >= "armv7"`,
    `Archi.thumb2_support`, `Clflags.option_Osize`) is the argument
    `Constantexpand.Options`.
  * The pools list the constants in the order in which their labels were
    created (OCaml's order is that of `Hashtbl.fold`, which is unspecified);
    as in OCaml, single-precision constants come first, then
    double-precision constants, then symbols.
-/
import CCLib.arm.Asm
import CCLib.backend.Asmexpandaux

namespace CC
namespace Arm
namespace Constantexpand

open Asm Asmexpandaux

instance : AsmInstr Instruction where
  labelOf | .Plabel l => some l | _ => none
  mkLabel := .Plabel
  annotKind | .Pbuiltin (.EF_annot kind _ _) _ _ => some kind | _ => none
  isDebug | .Pbuiltin (.EF_debug _ _ _) _ _ => true | _ => false
  mkBuiltin ef := .Pbuiltin ef [] .BR_none

/-- The expansion monad for ARM code. -/
abbrev EM := Asmexpandaux.M Instruction

/-- The configuration used by the constant expansion. -/
structure Options where
  /-- `vfpv3` (`Configuration.model >= "armv7"`) -/
  vfpv3 : Bool := true
  /-- `Archi.thumb2_support` -/
  thumb2Support : Bool := true
  /-- `Clflags.option_Osize` -/
  osize : Bool := false

/-- OCaml's `max_int` on 64-bit platforms. -/
def maxInt : Int := 2 ^ 62 - 1

/-- The global state of `Constantexpand.ml`. -/
structure State where
  /-- `currpos`: current code position (in bytes) -/
  currpos : Int := 0
  /-- `size_constants`: size of the constants waiting to be emitted -/
  sizeConstants : Int := 0
  /-- `max_pos_constants`: latest position at which the pool must be emitted -/
  maxPosConstants : Int := maxInt
  /-- `float_labels` (keyed by the bits of the float), in creation order -/
  floatLabels : List (Integers.Int64 × Floats.Float × Label) := []
  /-- `float32_labels` (keyed by the bits of the float), in creation order -/
  float32Labels : List (Integers.Int × Floats.Float32 × Label) := []
  /-- `symbol_labels`, in creation order -/
  symbolLabels : List ((Ident × Integers.Ptrofs) × Label) := []

/-- The constant-expansion monad. -/
abbrev CM := StateT State EM

/-- `distance_to_emit_constants` -/
def distanceToEmitConstants : CM Int := do
  let s ← get
  return s.maxPosConstants - (s.currpos + s.sizeConstants)

/-- Record that a new constant of size `sz` must be reachable within `pinc`
    bytes (the second half of `get_label`). -/
def recordConstant (sz pinc : Int) : CM Unit :=
  modify fun s => { s with
    sizeConstants := s.sizeConstants + sz
    maxPosConstants := min s.maxPosConstants (s.currpos + pinc) }

/-- `label_float` -/
def labelFloat (f : Floats.Float) : CM Label := do
  let key := Floats.Float.toBits f
  match ((← get).floatLabels.find? (·.1 == key)) with
  | some (_, _, l) => return l
  | none =>
    let l ← (newLabel : EM Label)
    modify fun s => { s with floatLabels := s.floatLabels ++ [(key, f, l)] }
    recordConstant 8 1024
    return l

/-- `label_float32` -/
def labelFloat32 (f : Floats.Float32) : CM Label := do
  let key := Floats.Float32.toBits f
  match ((← get).float32Labels.find? (·.1 == key)) with
  | some (_, _, l) => return l
  | none =>
    let l ← (newLabel : EM Label)
    modify fun s => { s with float32Labels := s.float32Labels ++ [(key, f, l)] }
    recordConstant 4 1024
    return l

/-- `label_symbol` -/
def labelSymbol (id : Ident) (ofs : Integers.Ptrofs) : CM Label := do
  match ((← get).symbolLabels.find? (·.1 == (id, ofs))) with
  | some (_, l) => return l
  | none =>
    let l ← (newLabel : EM Label)
    modify fun s => { s with symbolLabels := s.symbolLabels ++ [((id, ofs), l)] }
    recordConstant 4 4096
    return l

/-- `reset_constants` -/
def resetConstants : CM Unit :=
  modify fun s => { s with
    floatLabels := [], float32Labels := [], symbolLabels := []
    sizeConstants := 0, maxPosConstants := maxInt }

/-- `is_immediate_float64`: the double can be encoded in a `vmov` (1 sign
    bit, 4 bits of fraction, a 3-bit exponent). -/
def isImmediateFloat64 (bits : Integers.Int64) : Bool :=
  let u := Integers.Int64.unsigned bits
  let exp := (u / 2 ^ 52) % 2048 - 1023
  let mant := u % 2 ^ 52
  (-3 ≤ exp) && exp ≤ 4 && mant % 2 ^ 48 = 0

/-- `is_immediate_float32` -/
def isImmediateFloat32 (bits : Integers.Int) : Bool :=
  let u := Integers.Int.unsigned bits
  let exp := (u / 2 ^ 23) % 256 - 127
  let mant := u % 2 ^ 23
  (-3 ≤ exp) && exp ≤ 4 && mant % 2 ^ 19 = 0

/-- `no_fallthrough` -/
def noFallthrough : Instruction → Bool
  | .Pb _ | .Pbsymb _ _ | .Pbreg _ _ => true
  | _ => false

/-- `estimate_size`: an upper bound on the number of 4-byte words of an
    instruction. -/
def estimateSize : Instruction → Int
  | .Pflid _ _ | .Pflis _ _ => 3
  | .Pfcmpd _ _ | .Pfcmpzd _ | .Pfsitod _ _ | .Pfuitod _ _ | .Pftosizd _ _ | .Pftouizd _ _
  | .Pfcmps _ _ | .Pfcmpzs _ | .Pfsitos _ _ | .Pfuitos _ _ | .Pftosizs _ _ | .Pftouizs _ _
  | .Pmovite _ _ _ _ => 2
  | .Pbuiltin ef _ _ =>
    match ef with
    | .EF_inline_asm _ _ _ => 256
    | _ => 0
  | .Pcfi_adjust _ | .Pcfi_rel_offset _ | .Plabel _ => 0
  | .Pbtbl _ tbl => 2 + tbl.length
  | _ => 1

/-- `expand_constants ()`: emit the pending constants as a literal pool. -/
def expandPendingConstants : CM Unit := do
  let s ← get
  let consts : List CodeConstant :=
    s.float32Labels.map (fun (_, f, l) => .Float32 l f) ++
    s.floatLabels.map (fun (_, f, l) => .Float64 l f) ++
    s.symbolLabels.map (fun ((id, ofs), l) => .Symbol l id ofs)
  if !consts.isEmpty then (emit (.Pconstants consts) : EM Unit)
  resetConstants

/-- `expand_instruction`: returns the number of words of the emitted code. -/
def expandInstruction (o : Options) : Instruction → CM Int
  | .Pflid r1 f => do
    if o.vfpv3 && isImmediateFloat64 (Floats.Float.toBits f) then
      (emit (.Pflid_imm r1 f) : EM Unit)
    else
      let lbl ← labelFloat f
      (emit (.Pflid_lbl r1 lbl f) : EM Unit)
    return 1
  | .Pflis r1 f => do
    if o.vfpv3 && isImmediateFloat32 (Floats.Float32.toBits f) then
      (emit (.Pflis_imm r1 f) : EM Unit)
    else
      let lbl ← labelFloat32 f
      (emit (.Pflis_lbl r1 lbl f) : EM Unit)
    return 1
  | .Ploadsymbol r1 id ofs => do
    let n := Integers.Ptrofs.signed ofs
    if -32768 ≤ n && n ≤ 32767 && o.thumb2Support && !o.osize then
      (emit (.Ploadsymbol_imm r1 id ofs) : EM Unit)
      return 2
    else
      let lbl ← labelSymbol id ofs
      (emit (.Ploadsymbol_lbl r1 lbl id ofs) : EM Unit)
      return 1
  | inst => do
    (emit inst : EM Unit)
    return estimateSize inst

/-- `expand_instructions` -/
def expandInstructions (o : Options) : Bool → List Instruction → CM Unit
  | _, [] => pure ()
  | noFall, i :: il => do
    let estimate := estimateSize i * 4
    let d := (← distanceToEmitConstants) - estimate
    if d < 256 && noFall then
      expandPendingConstants
    else if d < 16 then
      let lbl ← (newLabel : EM Label)
      (emit (.Pb lbl) : EM Unit)
      expandPendingConstants
      (emit (.Plabel lbl) : EM Unit)
    let n ← expandInstruction o i
    modify fun s => { s with currpos := s.currpos + n * 4 }
    expandInstructions o (noFallthrough i) il

/-- `expand_constants fn`: insert the literal pools in the code of a
    function. -/
def expandConstants (o : Options) (fn : Asm.Function) : EM Asm.Function := do
  let run : CM (List Instruction) := do
    resetConstants
    (setCurrentFunction fn.fn_sig fn.fn_code : EM Unit)
    expandInstructions o false fn.fn_code
    expandPendingConstants
    (getCurrentFunction : EM (List Instruction))
  let code ← run.run' {}
  return { fn with fn_code := code }

end Constantexpand
end Arm
end CC
