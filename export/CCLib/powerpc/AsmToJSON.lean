/-
  Output of the PowerPC `Asm` program in JSON format (option `-sdump`) —
  port of `powerpc/AsmToJSON.ml`.

  Differences from OCaml:
  * Printing happens in the monad `Json.M` (see `backend/Json.lean`).
  * OCaml's `assert false` on instructions that cannot occur after
    `Asmexpand` (`Pallocframe`, `Pfreeframe`, `Pextzw`, `Pfcfl`, `Pfcti`,
    `Pfctid`, `Pfmake`, `Pfxdp`, `Pfsel_gen`, `Plmake`, `Pllo`, `Plhi`,
    `Pmfcrbit`, non-exported built-ins; the `.cfi` directives and the
    annotations without JSON form are filtered out beforehand) prints
    nothing here.
  * The warning `Inline_asm_sdump` ("inline assembler is not supported in
    sdump") is not emitted: the instruction is printed as `Pinlineasm`.
  * Integers are printed as in OCaml: `pp_int` (used for `Cint` and symbol
    offsets) prints the low 32 bits, signed; `pp_int64` of a 32-bit
    `Int.int` prints its unsigned value and of an `Int64.int` its signed
    value.  OCaml builds `Constant (Cint n)` from the 64-bit immediates of
    `Paddi64`, … (an untyped `Z`); here these are the argument `CintL n`,
    printed the same way.
  * `print_if` takes the destination file, the compile information and the
    atom properties as arguments (OCaml reads global references and `C2C`).
-/
import CCLib.powerpc.TargetPrinter
import CCLib.backend.JsonAST

namespace CC
namespace PowerPC
namespace AsmToJSON

open Asm Json

/-- `pp_int` of an integer: its low 32 bits, signed. -/
def ppIntZ (n : Int) : M Unit := ppInt (Integers.Int.repr n)

/-- `AsmToJSON.pp_reg` -/
def ppReg (t n : String) : M Unit := ppJsingleObject "Register" ppJstring (t ++ n)

/-- `AsmToJSON.pp_ireg` -/
def ppIreg (r : Asm.Ireg) : M Unit := ppReg "r" (TargetPrinter.intRegName r)
/-- `AsmToJSON.pp_freg` -/
def ppFreg (r : Asm.Freg) : M Unit := ppReg "f" (TargetPrinter.floatRegName r)

/-- `AsmToJSON.preg_annot` -/
def pregAnnot : Preg → String
  | .IR r => "r" ++ TargetPrinter.intRegName r
  | .FR r => "f" ++ TargetPrinter.floatRegName r
  | _ => "<bad register>"

/-- `AsmToJSON.pp_constant` -/
def ppConstant (c : Asm.Constant) : M Unit :=
  let ppSymbol : Ident × Integers.Ptrofs → M Unit := fun (i, c) => do
    ppJobjectStart
    ppJmember "Name" ppAtom i (first := true)
    ppJmember "Offset" ppIntZ (Integers.Ptrofs.unsigned c)
    ppJobjectEnd
  match c with
  | .Cint i => ppIntConstant i
  | .Csymbol_low i c => ppJsingleObject "Symbol_low" ppSymbol (i, c)
  | .Csymbol_high i c => ppJsingleObject "Symbol_high" ppSymbol (i, c)
  | .Csymbol_sda i c => ppJsingleObject "Symbol_sda" ppSymbol (i, c)
  | .Csymbol_rel_low i c => ppJsingleObject "Symbol_rel_low" ppSymbol (i, c)
  | .Csymbol_rel_high i c => ppJsingleObject "Symbol_rel_high" ppSymbol (i, c)

/-- `AsmToJSON.pp_crbit` -/
def ppCrbit (c : Asm.Crbit) : M Unit := ppJsingleObject "CRbit" ppJint (TargetPrinter.numCrbit c)

/-- `AsmToJSON.pp_label` -/
def ppLabel (l : Positive) : M Unit := ppJsingleObject "Label" ppJint32 l.toNat

/-- `AsmToJSON.instruction_arg` -/
inductive InstructionArg where
  | Ireg (r : Asm.Ireg)
  | Freg (r : Asm.Freg)
  | Constant (c : Asm.Constant)
  /-- `Constant (Cint n)` for a 64-bit immediate `n` -/
  | CintL (n : Integers.Int64)
  /-- `Long i`, with the value printed by `pp_int64` -/
  | Long (i : Int)
  | Id
  | Crbit (c : Asm.Crbit)
  | ALabel (l : Positive)
  | Float32 (f : Floats.Float32)
  | Float64 (f : Floats.Float)
  | Atom (a : Positive)
  | String (s : _root_.String)

/-- `AsmToJSON.pp_arg` -/
def ppArg : InstructionArg → M Unit
  | .Ireg ir => ppIreg ir
  | .Freg fr => ppFreg fr
  | .Constant c => ppConstant c
  | .CintL n => ppJsingleObject "Integer" ppIntZ (Integers.Int64.unsigned n)
  | .Long i => ppJsingleObject "Integer" ppJint64 i
  | .Id => ppIdConst
  | .Crbit cr => ppCrbit cr
  | .ALabel lbl => ppLabel lbl
  | .Float32 f => ppFloat32Constant f
  | .Float64 f => ppFloat64Constant f
  | .Atom a => ppAtomConstant a
  | .String s => ppJsingleObject "String" ppJstring s

/-- `AsmToJSON.mnemonic_names` (`StringSet.elements`: sorted) -/
def mnemonicNames : List String :=
  ["Padd", "Paddc", "Padde", "Paddi", "Paddic", "Paddis", "Paddze", "Pand_", "Pandc",
    "Pandi_", "Pandis_", "Pannot", "Pb", "Pbctr", "Pbctrl", "Pbdnz", "Pbf", "Pbl", "Pblr",
    "Pbs", "Pbt", "Pbtbl", "Pcmpb", "Pcmpd", "Pcmpdi", "Pcmpld", "Pcmpldi", "Pcmplw",
    "Pcmplwi", "Pcmpw", "Pcmpwi", "Pcntlzd", "Pcntlzw", "Pcreqv", "Pcror", "Pcrxor", "Pdcbf",
    "Pdcbi", "Pdcbt", "Pdcbtls", "Pdcbtst", "Pdcbz", "Pdivd", "Pdivdu", "Pdivw", "Pdivwu",
    "Peieio", "Peqv", "Pextsb", "Pextsh", "Pextsw", "Pfabs", "Pfadd", "Pfadds", "Pfcfid",
    "Pfcmpu", "Pfctidz", "Pfctiw", "Pfctiwz", "Pfdiv", "Pfdivs", "Pfmadd", "Pfmr", "Pfmsub",
    "Pfmul", "Pfmuls", "Pfneg", "Pfnmadd", "Pfnmsub", "Pfres", "Pfrsp", "Pfrsqrte", "Pfsel",
    "Pfsqrt", "Pfsub", "Pfsubs", "Picbi", "Picbtls", "Pinlineasm", "Pisel", "Pisync", "Plabel",
    "Plbz", "Plbzx", "Pld", "Pldbrx", "Pldi", "Pldx", "Plfd", "Plfdx", "Plfi", "Plfis", "Plfs",
    "Plfsx", "Plha", "Plhax", "Plhbrx", "Plhz", "Plhzx", "Plwarx", "Plwbrx", "Plwsync", "Plwz",
    "Plwzu", "Plwzx", "Pmbar", "Pmfcr", "Pmflr", "Pmfspr", "Pmr", "Pmtctr", "Pmtlr", "Pmtspr",
    "Pmulhd", "Pmulhdu", "Pmulhw", "Pmulhwu", "Pmulld", "Pmulli", "Pmullw", "Pnand", "Pnor",
    "Por", "Porc", "Pori", "Poris", "Prldicl", "Prldimi", "Prldinm", "Prlwimi", "Prlwinm",
    "Psld", "Pslw", "Psrad", "Psradi", "Psraw", "Psrawi", "Psrd", "Psrw", "Pstb", "Pstbx",
    "Pstd", "Pstdbrx", "Pstdu", "Pstdx", "Pstfd", "Pstfdu", "Pstfdx", "Pstfs", "Pstfsx",
    "Psth", "Psthbrx", "Psthx", "Pstw", "Pstwbrx", "Pstwcx_", "Pstwu", "Pstwux", "Pstwx",
    "Psubfc", "Psubfe", "Psubfic", "Psubfze", "Psync", "Ptrap", "Pxor", "Pxori", "Pxoris"]

/-- The JSON form of an annotation of kind 2 (`AisAnnot.json_ais_annot`). -/
def jsonAnnot (txt : _root_.String) (args : List (BuiltinArg Preg)) : List AisAnnot.T :=
  match AisAnnot.jsonAisAnnot pregAnnot "r1" txt args with
  | .ok l => l
  | .error _ => []

/-- `instruction pp n args` of `pp_instructions` -/
def ppInstr (n : _root_.String) (args : List InstructionArg) : M Unit := do
  ppJobjectStart
  ppJmember "Instruction Name" ppJstring n (first := true)
  ppJmember "Args" (ppJarray ppArg) args
  ppJobjectEnd

/-- `instruction pp` of `pp_instructions`: one instruction. -/
def ppInstruction : Instruction → M Unit
  | .Padd ir1 ir2 ir3 | .Padd64 ir1 ir2 ir3 => ppInstr "Padd" [.Ireg ir1, .Ireg ir2, .Ireg ir3]
  | .Paddc ir1 ir2 ir3 => ppInstr "Paddc" [.Ireg ir1, .Ireg ir2, .Ireg ir3]
  | .Padde ir1 ir2 ir3 => ppInstr "Padde" [.Ireg ir1, .Ireg ir2, .Ireg ir3]
  | .Paddi ir1 ir2 c => ppInstr "Paddi" [.Ireg ir1, .Ireg ir2, .Constant c]
  | .Paddi64 ir1 ir2 n => ppInstr "Paddi" [.Ireg ir1, .Ireg ir2, .CintL n]
  | .Paddic ir1 ir2 c => ppInstr "Paddic" [.Ireg ir1, .Ireg ir2, .Constant c]
  | .Paddis ir1 ir2 c => ppInstr "Paddis" [.Ireg ir1, .Ireg ir2, .Constant c]
  | .Paddis64 ir1 ir2 n => ppInstr "Paddis" [.Ireg ir1, .Ireg ir2, .CintL n]
  | .Paddze ir1 ir2 | .Paddze64 ir1 ir2 => ppInstr "Paddze" [.Ireg ir1, .Ireg ir2]
  | .Pallocframe _ _ _ => pure ()
  | .Pand_ ir1 ir2 ir3 | .Pand_64 ir1 ir2 ir3 => ppInstr "Pand_" [.Ireg ir1, .Ireg ir2, .Ireg ir3]
  | .Pandc ir1 ir2 ir3 => ppInstr "Pandc" [.Ireg ir1, .Ireg ir2, .Ireg ir3]
  | .Pandi_ ir1 ir2 c => ppInstr "Pandi_" [.Ireg ir1, .Ireg ir2, .Constant c]
  | .Pandi_64 ir1 ir2 n => ppInstr "Pandi_" [.Ireg ir1, .Ireg ir2, .CintL n]
  | .Pandis_ ir1 ir2 c => ppInstr "Pandis_" [.Ireg ir1, .Ireg ir2, .Constant c]
  | .Pandis_64 ir1 ir2 n => ppInstr "Pandis_" [.Ireg ir1, .Ireg ir2, .CintL n]
  | .Pb l => ppInstr "Pb" [.ALabel l]
  | .Pbctr _ => ppInstr "Pbctr" []
  | .Pbctrl _ => ppInstr "Pbctrl" []
  | .Pbdnz l => ppInstr "Pbdnz" [.ALabel l]
  | .Pbf cr l => ppInstr "Pbf" [.Crbit cr, .ALabel l]
  | .Pbl i _ => ppInstr "Pbl" [.Atom i]
  | .Pbs i _ => ppInstr "Pbs" [.Atom i]
  | .Pblr => ppInstr "Pblr" []
  | .Pbt cr l => ppInstr "Pbt" [.Crbit cr, .ALabel l]
  | .Pbtbl i lb => ppInstr "Pbtbl" (.Ireg i :: lb.map .ALabel)
  | .Pcmpb ir1 ir2 ir3 => ppInstr "Pcmpb" [.Ireg ir1, .Ireg ir2, .Ireg ir3]
  | .Pcmpld ir1 ir2 => ppInstr "Pcmpld" [.Ireg ir1, .Ireg ir2]
  | .Pcmpldi ir n => ppInstr "Pcmpldi" [.Ireg ir, .CintL n]
  | .Pcmplw ir1 ir2 => ppInstr "Pcmplw" [.Ireg ir1, .Ireg ir2]
  | .Pcmplwi ir c => ppInstr "Pcmplwi" [.Ireg ir, .Constant c]
  | .Pcmpd ir1 ir2 => ppInstr "Pcmpd" [.Ireg ir1, .Ireg ir2]
  | .Pcmpdi ir n => ppInstr "Pcmpdi" [.Ireg ir, .CintL n]
  | .Pcmpw ir1 ir2 => ppInstr "Pcmpw" [.Ireg ir1, .Ireg ir2]
  | .Pcmpwi ir c => ppInstr "Pcmpwi" [.Ireg ir, .Constant c]
  | .Pcntlzd ir1 ir2 => ppInstr "Pcntlzd" [.Ireg ir1, .Ireg ir2]
  | .Pcntlzw ir1 ir2 => ppInstr "Pcntlzw" [.Ireg ir1, .Ireg ir2]
  | .Pcreqv cr1 cr2 cr3 => ppInstr "Pcreqv" [.Crbit cr1, .Crbit cr2, .Crbit cr3]
  | .Pcror cr1 cr2 cr3 => ppInstr "Pcror" [.Crbit cr1, .Crbit cr2, .Crbit cr3]
  | .Pcrxor cr1 cr2 cr3 => ppInstr "Pcrxor" [.Crbit cr1, .Crbit cr2, .Crbit cr3]
  | .Pdcbf ir1 ir2 => ppInstr "Pdcbf" [.Ireg ir1, .Ireg ir2]
  | .Pdcbi ir1 ir2 => ppInstr "Pdcbi" [.Ireg ir1, .Ireg ir2]
  | .Pdcbt n ir1 ir2 => ppInstr "Pdcbt" [.Constant (.Cint n), .Ireg ir1, .Ireg ir2]
  | .Pdcbtst n ir1 ir2 => ppInstr "Pdcbtst" [.Constant (.Cint n), .Ireg ir1, .Ireg ir2]
  | .Pdcbtls n ir1 ir2 => ppInstr "Pdcbtls" [.Constant (.Cint n), .Ireg ir1, .Ireg ir2]
  | .Pdcbz ir1 ir2 => ppInstr "Pdcbz" [.Ireg ir1, .Ireg ir2]
  | .Pdivw ir1 ir2 ir3 => ppInstr "Pdivw" [.Ireg ir1, .Ireg ir2, .Ireg ir3]
  | .Pdivd ir1 ir2 ir3 => ppInstr "Pdivd" [.Ireg ir1, .Ireg ir2, .Ireg ir3]
  | .Pdivwu ir1 ir2 ir3 => ppInstr "Pdivwu" [.Ireg ir1, .Ireg ir2, .Ireg ir3]
  | .Pdivdu ir1 ir2 ir3 => ppInstr "Pdivdu" [.Ireg ir1, .Ireg ir2, .Ireg ir3]
  | .Peieio => ppInstr "Peieio" []
  | .Peqv ir1 ir2 ir3 => ppInstr "Peqv" [.Ireg ir1, .Ireg ir2, .Ireg ir3]
  | .Pextsb ir1 ir2 => ppInstr "Pextsb" [.Ireg ir1, .Ireg ir2]
  | .Pextsh ir1 ir2 => ppInstr "Pextsh" [.Ireg ir1, .Ireg ir2]
  | .Pextsw ir1 ir2 => ppInstr "Pextsw" [.Ireg ir1, .Ireg ir2]
  | .Pextzw _ _ => pure ()
  | .Pfreeframe _ _ => pure ()
  | .Pfabs fr1 fr2 | .Pfabss fr1 fr2 => ppInstr "Pfabs" [.Freg fr1, .Freg fr2]
  | .Pfadd fr1 fr2 fr3 => ppInstr "Pfadd" [.Freg fr1, .Freg fr2, .Freg fr3]
  | .Pfadds fr1 fr2 fr3 => ppInstr "Pfadds" [.Freg fr1, .Freg fr2, .Freg fr3]
  | .Pfcmpu fr1 fr2 => ppInstr "Pfcmpu" [.Freg fr1, .Freg fr2]
  | .Pfcfl _ _ => pure ()
  | .Pfcfid fr1 fr2 => ppInstr "Pfcfid" [.Freg fr1, .Freg fr2]
  | .Pfcti _ _ | .Pfctid _ _ => pure ()
  | .Pfctidz fr1 fr2 => ppInstr "Pfctidz" [.Freg fr1, .Freg fr2]
  | .Pfctiw fr1 fr2 => ppInstr "Pfctiw" [.Freg fr1, .Freg fr2]
  | .Pfctiwz fr1 fr2 => ppInstr "Pfctiwz" [.Freg fr1, .Freg fr2]
  | .Pfdiv fr1 fr2 fr3 => ppInstr "Pfdiv" [.Freg fr1, .Freg fr2, .Freg fr3]
  | .Pfdivs fr1 fr2 fr3 => ppInstr "Pfdivs" [.Freg fr1, .Freg fr2, .Freg fr3]
  | .Pfmake _ _ _ => pure ()
  | .Pfmr fr1 fr2 => ppInstr "Pfmr" [.Freg fr1, .Freg fr2]
  | .Pfmul fr1 fr2 fr3 => ppInstr "Pfmul" [.Freg fr1, .Freg fr2, .Freg fr3]
  | .Pfmuls fr1 fr2 fr3 => ppInstr "Pfmuls" [.Freg fr1, .Freg fr2, .Freg fr3]
  | .Pfneg fr1 fr2 | .Pfnegs fr1 fr2 => ppInstr "Pfneg" [.Freg fr1, .Freg fr2]
  | .Pfrsp fr1 fr2 => ppInstr "Pfrsp" [.Freg fr1, .Freg fr2]
  | .Pfxdp _ _ => pure ()
  | .Pfsub fr1 fr2 fr3 => ppInstr "Pfsub" [.Freg fr1, .Freg fr2, .Freg fr3]
  | .Pfsubs fr1 fr2 fr3 => ppInstr "Pfsubs" [.Freg fr1, .Freg fr2, .Freg fr3]
  | .Pfmadd fr1 fr2 fr3 fr4 => ppInstr "Pfmadd" [.Freg fr1, .Freg fr2, .Freg fr3, .Freg fr4]
  | .Pfmsub fr1 fr2 fr3 fr4 => ppInstr "Pfmsub" [.Freg fr1, .Freg fr2, .Freg fr3, .Freg fr4]
  | .Pfnmadd fr1 fr2 fr3 fr4 => ppInstr "Pfnmadd" [.Freg fr1, .Freg fr2, .Freg fr3, .Freg fr4]
  | .Pfnmsub fr1 fr2 fr3 fr4 => ppInstr "Pfnmsub" [.Freg fr1, .Freg fr2, .Freg fr3, .Freg fr4]
  | .Pfsqrt fr1 fr2 => ppInstr "Pfsqrt" [.Freg fr1, .Freg fr2]
  | .Pfrsqrte fr1 fr2 => ppInstr "Pfrsqrte" [.Freg fr1, .Freg fr2]
  | .Pfres fr1 fr2 => ppInstr "Pfres" [.Freg fr1, .Freg fr2]
  | .Pfsel fr1 fr2 fr3 fr4 => ppInstr "Pfsel" [.Freg fr1, .Freg fr2, .Freg fr3, .Freg fr4]
  | .Pisel ir1 ir2 ir3 cr => ppInstr "Pisel" [.Ireg ir1, .Ireg ir2, .Ireg ir3, .Crbit cr]
  | .Pfsel_gen _ _ _ _ => pure ()
  | .Picbi ir1 ir2 => ppInstr "Picbi" [.Ireg ir1, .Ireg ir2]
  | .Picbtls n ir1 ir2 => ppInstr "Picbtls" [.Constant (.Cint n), .Ireg ir1, .Ireg ir2]
  | .Pisync => ppInstr "Pisync" []
  | .Plwsync => ppInstr "Plwsync" []
  | .Plbz ir1 c ir2 => ppInstr "Plbz" [.Ireg ir1, .Constant c, .Ireg ir2]
  | .Plbzx ir1 ir2 ir3 => ppInstr "Plbzx" [.Ireg ir1, .Ireg ir2, .Ireg ir3]
  | .Pld ir1 c ir2 | .Pld_a ir1 c ir2 => ppInstr "Pld" [.Ireg ir1, .Constant c, .Ireg ir2]
  | .Pldbrx ir1 ir2 ir3 => ppInstr "Pldbrx" [.Ireg ir1, .Ireg ir2, .Ireg ir3]
  | .Pldx ir1 ir2 ir3 | .Pldx_a ir1 ir2 ir3 => ppInstr "Pldx" [.Ireg ir1, .Ireg ir2, .Ireg ir3]
  | .Plfd fr c ir | .Plfd_a fr c ir => ppInstr "Plfd" [.Freg fr, .Constant c, .Ireg ir]
  | .Plfdx fr ir1 ir2 | .Plfdx_a fr ir1 ir2 => ppInstr "Plfdx" [.Freg fr, .Ireg ir1, .Ireg ir2]
  | .Plfs fr c ir => ppInstr "Plfs" [.Freg fr, .Constant c, .Ireg ir]
  | .Plfsx fr ir1 ir2 => ppInstr "Plfsx" [.Freg fr, .Ireg ir1, .Ireg ir2]
  | .Plha ir1 c ir2 => ppInstr "Plha" [.Ireg ir1, .Constant c, .Ireg ir2]
  | .Plhax ir1 ir2 ir3 => ppInstr "Plhax" [.Ireg ir1, .Ireg ir2, .Ireg ir3]
  | .Plhbrx ir1 ir2 ir3 => ppInstr "Plhbrx" [.Ireg ir1, .Ireg ir2, .Ireg ir3]
  | .Plhz ir1 c ir2 => ppInstr "Plhz" [.Ireg ir1, .Constant c, .Ireg ir2]
  | .Plhzx ir1 ir2 ir3 => ppInstr "Plhzx" [.Ireg ir1, .Ireg ir2, .Ireg ir3]
  | .Pldi ir c => ppInstr "Pldi" [.Ireg ir, .Long (Integers.Int64.signed c)]
  | .Plmake _ _ _ | .Pllo _ | .Plhi _ _ => pure ()
  | .Plfi fr fc => ppInstr "Plfi" [.Freg fr, .Float64 fc]
  | .Plfis fr fc => ppInstr "Plfis" [.Freg fr, .Float32 fc]
  | .Plwz ir1 c ir2 | .Plwz_a ir1 c ir2 => ppInstr "Plwz" [.Ireg ir1, .Constant c, .Ireg ir2]
  | .Plwzu ir1 c ir2 => ppInstr "Plwzu" [.Ireg ir1, .Constant c, .Ireg ir2]
  | .Plwzx ir1 ir2 ir3 | .Plwzx_a ir1 ir2 ir3 => ppInstr "Plwzx" [.Ireg ir1, .Ireg ir2, .Ireg ir3]
  | .Plwarx ir1 ir2 ir3 => ppInstr "Plwarx" [.Ireg ir1, .Ireg ir2, .Ireg ir3]
  | .Plwbrx ir1 ir2 ir3 => ppInstr "Plwbrx" [.Ireg ir1, .Ireg ir2, .Ireg ir3]
  | .Pmbar c => ppInstr "Pmbar" [.Constant (.Cint c)]
  | .Pmfcr ir => ppInstr "Pmfcr" [.Ireg ir]
  | .Pmfcrbit _ _ => pure ()
  | .Pmflr ir => ppInstr "Pmflr" [.Ireg ir]
  | .Pmr ir1 ir2 => ppInstr "Pmr" [.Ireg ir1, .Ireg ir2]
  | .Pmtctr ir => ppInstr "Pmtctr" [.Ireg ir]
  | .Pmtlr ir => ppInstr "Pmtlr" [.Ireg ir]
  | .Pmfspr ir n => ppInstr "Pmfspr" [.Ireg ir, .Constant (.Cint n)]
  | .Pmtspr n ir => ppInstr "Pmtspr" [.Constant (.Cint n), .Ireg ir]
  | .Pmulhd ir1 ir2 ir3 => ppInstr "Pmulhd" [.Ireg ir1, .Ireg ir2, .Ireg ir3]
  | .Pmulhdu ir1 ir2 ir3 => ppInstr "Pmulhdu" [.Ireg ir1, .Ireg ir2, .Ireg ir3]
  | .Pmulld ir1 ir2 ir3 => ppInstr "Pmulld" [.Ireg ir1, .Ireg ir2, .Ireg ir3]
  | .Pmulli ir1 ir2 c => ppInstr "Pmulli" [.Ireg ir1, .Ireg ir2, .Constant c]
  | .Pmullw ir1 ir2 ir3 => ppInstr "Pmullw" [.Ireg ir1, .Ireg ir2, .Ireg ir3]
  | .Pmulhw ir1 ir2 ir3 => ppInstr "Pmulhw" [.Ireg ir1, .Ireg ir2, .Ireg ir3]
  | .Pmulhwu ir1 ir2 ir3 => ppInstr "Pmulhwu" [.Ireg ir1, .Ireg ir2, .Ireg ir3]
  | .Pnand ir1 ir2 ir3 => ppInstr "Pnand" [.Ireg ir1, .Ireg ir2, .Ireg ir3]
  | .Pnor ir1 ir2 ir3 | .Pnor64 ir1 ir2 ir3 => ppInstr "Pnor" [.Ireg ir1, .Ireg ir2, .Ireg ir3]
  | .Por ir1 ir2 ir3 | .Por64 ir1 ir2 ir3 => ppInstr "Por" [.Ireg ir1, .Ireg ir2, .Ireg ir3]
  | .Porc ir1 ir2 ir3 => ppInstr "Porc" [.Ireg ir1, .Ireg ir2, .Ireg ir3]
  | .Pori ir1 ir2 c => ppInstr "Pori" [.Ireg ir1, .Ireg ir2, .Constant c]
  | .Pori64 ir1 ir2 n => ppInstr "Pori" [.Ireg ir1, .Ireg ir2, .CintL n]
  | .Poris ir1 ir2 c => ppInstr "Poris" [.Ireg ir1, .Ireg ir2, .Constant c]
  | .Poris64 ir1 ir2 n => ppInstr "Poris" [.Ireg ir1, .Ireg ir2, .CintL n]
  | .Prldicl ir1 ir2 ic1 ic2 => ppInstr "Prldicl" [.Ireg ir1, .Ireg ir2, .Constant (.Cint ic1), .Constant (.Cint ic2)]
  | .Prldinm ir1 ir2 ic1 ic2 => ppInstr "Prldinm" [.Ireg ir1, .Ireg ir2, .Long (Integers.Int.unsigned ic1), .Long (Integers.Int64.signed ic2)]
  | .Prldimi ir1 ir2 ic1 ic2 => ppInstr "Prldimi" [.Ireg ir1, .Ireg ir2, .Long (Integers.Int.unsigned ic1), .Long (Integers.Int64.signed ic2)]
  | .Prlwinm ir1 ir2 ic1 ic2 => ppInstr "Prlwinm" [.Ireg ir1, .Ireg ir2, .Constant (.Cint ic1), .Constant (.Cint ic2)]
  | .Prlwimi ir1 ir2 ic1 ic2 => ppInstr "Prlwimi" [.Ireg ir1, .Ireg ir2, .Constant (.Cint ic1), .Constant (.Cint ic2)]
  | .Psld ir1 ir2 ir3 => ppInstr "Psld" [.Ireg ir1, .Ireg ir2, .Ireg ir3]
  | .Pslw ir1 ir2 ir3 => ppInstr "Pslw" [.Ireg ir1, .Ireg ir2, .Ireg ir3]
  | .Psrad ir1 ir2 ir3 => ppInstr "Psrad" [.Ireg ir1, .Ireg ir2, .Ireg ir3]
  | .Psradi ir1 ir2 ic => ppInstr "Psradi" [.Ireg ir1, .Ireg ir2, .Constant (.Cint ic)]
  | .Psraw ir1 ir2 ir3 => ppInstr "Psraw" [.Ireg ir1, .Ireg ir2, .Ireg ir3]
  | .Psrawi ir1 ir2 ic => ppInstr "Psrawi" [.Ireg ir1, .Ireg ir2, .Constant (.Cint ic)]
  | .Psrd ir1 ir2 ir3 => ppInstr "Psrd" [.Ireg ir1, .Ireg ir2, .Ireg ir3]
  | .Psrw ir1 ir2 ir3 => ppInstr "Psrw" [.Ireg ir1, .Ireg ir2, .Ireg ir3]
  | .Pstb ir1 c ir2 => ppInstr "Pstb" [.Ireg ir1, .Constant c, .Ireg ir2]
  | .Pstbx ir1 ir2 ir3 => ppInstr "Pstbx" [.Ireg ir1, .Ireg ir2, .Ireg ir3]
  | .Pstd ir1 c ir2 | .Pstd_a ir1 c ir2 => ppInstr "Pstd" [.Ireg ir1, .Constant c, .Ireg ir2]
  | .Pstdbrx ir1 ir2 ir3 => ppInstr "Pstdbrx" [.Ireg ir1, .Ireg ir2, .Ireg ir3]
  | .Pstdx ir1 ir2 ir3 | .Pstdx_a ir1 ir2 ir3 => ppInstr "Pstdx" [.Ireg ir1, .Ireg ir2, .Ireg ir3]
  | .Pstdu ir1 c ir2 => ppInstr "Pstdu" [.Ireg ir1, .Constant c, .Ireg ir2]
  | .Pstfd fr c ir | .Pstfd_a fr c ir => ppInstr "Pstfd" [.Freg fr, .Constant c, .Ireg ir]
  | .Pstfdu fr c ir => ppInstr "Pstfdu" [.Freg fr, .Constant c, .Ireg ir]
  | .Pstfdx fr ir1 ir2 | .Pstfdx_a fr ir1 ir2 => ppInstr "Pstfdx" [.Freg fr, .Ireg ir1, .Ireg ir2]
  | .Pstfs fr c ir => ppInstr "Pstfs" [.Freg fr, .Constant c, .Ireg ir]
  | .Pstfsx fr ir1 ir2 => ppInstr "Pstfsx" [.Freg fr, .Ireg ir1, .Ireg ir2]
  | .Psth ir1 c ir2 => ppInstr "Psth" [.Ireg ir1, .Constant c, .Ireg ir2]
  | .Psthx ir1 ir2 ir3 => ppInstr "Psthx" [.Ireg ir1, .Ireg ir2, .Ireg ir3]
  | .Psthbrx ir1 ir2 ir3 => ppInstr "Psthbrx" [.Ireg ir1, .Ireg ir2, .Ireg ir3]
  | .Pstw ir1 c ir2 | .Pstw_a ir1 c ir2 => ppInstr "Pstw" [.Ireg ir1, .Constant c, .Ireg ir2]
  | .Pstwu ir1 c ir2 => ppInstr "Pstwu" [.Ireg ir1, .Constant c, .Ireg ir2]
  | .Pstwx ir1 ir2 ir3 | .Pstwx_a ir1 ir2 ir3 => ppInstr "Pstwx" [.Ireg ir1, .Ireg ir2, .Ireg ir3]
  | .Pstwux ir1 ir2 ir3 => ppInstr "Pstwux" [.Ireg ir1, .Ireg ir2, .Ireg ir3]
  | .Pstwbrx ir1 ir2 ir3 => ppInstr "Pstwbrx" [.Ireg ir1, .Ireg ir2, .Ireg ir3]
  | .Pstwcx_ ir1 ir2 ir3 => ppInstr "Pstwcx_" [.Ireg ir1, .Ireg ir2, .Ireg ir3]
  | .Psubfc ir1 ir2 ir3 | .Psubfc64 ir1 ir2 ir3 => ppInstr "Psubfc" [.Ireg ir1, .Ireg ir2, .Ireg ir3]
  | .Psubfe ir1 ir2 ir3 => ppInstr "Psubfe" [.Ireg ir1, .Ireg ir2, .Ireg ir3]
  | .Psubfze ir1 ir2 => ppInstr "Psubfze" [.Ireg ir1, .Ireg ir2]
  | .Psubfic ir1 ir2 c => ppInstr "Psubfic" [.Ireg ir1, .Ireg ir2, .Constant c]
  | .Psubfic64 ir1 ir2 n => ppInstr "Psubfic" [.Ireg ir1, .Ireg ir2, .CintL n]
  | .Psync => ppInstr "Psync" []
  | .Ptrap => ppInstr "Ptrap" []
  | .Pxor ir1 ir2 ir3 | .Pxor64 ir1 ir2 ir3 => ppInstr "Pxor" [.Ireg ir1, .Ireg ir2, .Ireg ir3]
  | .Pxori ir1 ir2 c => ppInstr "Pxori" [.Ireg ir1, .Ireg ir2, .Constant c]
  | .Pxori64 ir1 ir2 n => ppInstr "Pxori" [.Ireg ir1, .Ireg ir2, .CintL n]
  | .Pxoris ir1 ir2 c => ppInstr "Pxoris" [.Ireg ir1, .Ireg ir2, .Constant c]
  | .Pxoris64 ir1 ir2 n => ppInstr "Pxoris" [.Ireg ir1, .Ireg ir2, .CintL n]
  | .Plabel l => ppInstr "Plabel" [.ALabel l]
  | .Pbuiltin ef args _ =>
    match ef with
    | .EF_inline_asm _ _ _ => ppInstr "Pinlineasm" [.Id]
    | .EF_annot kind txt _ =>
      if kind.toNat = 2 then
        ppInstr "Pannot" ((jsonAnnot txt args).filterMap fun
          | .String s => some (.String s)
          | .Symbol s => some (.Atom s)
          | .Label _ => none)
      else pure ()
    | _ => pure ()
  | .Pcfi_adjust _ | .Pcfi_rel_offset _ => pure ()

/-- The instructions kept by `pp_instructions`. -/
def keepInstruction : Instruction → Bool
  | .Pbuiltin ef args _ =>
    match ef with
    | .EF_inline_asm _ _ _ => true
    | .EF_annot kind txt _ => kind.toNat = 2 && !(jsonAnnot txt args).isEmpty
    | _ => false
  | .Pcfi_adjust _ | .Pcfi_rel_offset _ => false
  | _ => true

/-- `AsmToJSON.pp_instructions` -/
def ppInstructions (ic : List Instruction) : M Unit :=
  ppJarray ppInstruction (ic.filter keepInstruction)

/-- `AsmToJSON.print_if`: write the JSON dump of `prog` to `destination`
    (in the folder `sdumpFolder`), if any. -/
def printIf (destination : Option _root_.String) (sdumpFolder : _root_.String)
    (info : JsonAST.CompileInfo) (atoms : PrintAsm.AtomInfo) (isInline : Ident → Bool)
    (prog : Asm.Program) (sourcename : _root_.String) : IO Unit :=
  match destination with
  | none => pure ()
  | some f => do
    let f := if sdumpFolder.isEmpty then f else sdumpFolder ++ "/" ++ f
    IO.FS.writeFile f
      (render (JsonAST.ppAst info atoms isInline Asm.Function.fn_code ppInstructions prog sourcename))

/-- `AsmToJSON.pp_mnemonics` -/
def ppMnemonics : M Unit := JsonAST.ppMnemonics mnemonicNames

#guard mnemonicNames.length = 168
#guard render (ppInstructions [.Paddi .GPR3 .GPR0 (.Cint (Integers.Int.repr (-1))), .Pblr]) =
  "[\n{ \"Instruction Name\" :\"Paddi\"\n, \"Args\" :[\n{ \"Register\" :\"r3\"\n}, " ++
  "\n{ \"Register\" :\"r0\"\n}, \n{ \"Integer\" :-1\n}]\n}, " ++
  "\n{ \"Instruction Name\" :\"Pblr\"\n, \"Args\" :[]\n}]"

end AsmToJSON
end PowerPC
end CC
