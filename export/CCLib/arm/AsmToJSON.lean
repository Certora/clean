/-
  Output of the ARM `Asm` program in JSON format (option `-sdump`) — port of
  `arm/AsmToJSON.ml`.

  Differences from OCaml:
  * Printing happens in the monad `Json.M` (see `backend/Json.lean`).
  * OCaml's `assert false` on instructions that cannot occur after
    `Asmexpand` (`Pallocframe`, `Pfreeframe`, `Pflid`, `Pflis`,
    `Ploadsymbol`, non-exported built-ins; the `.cfi` directives are
    filtered out beforehand) prints nothing here.
  * The warning `Inline_asm_sdump` ("inline assembler is not supported in
    sdump") is not emitted: the instruction is printed as `Pinlineasm`.
  * Integers are printed as in OCaml: `pp_int64`/`pp_z` of a 32-bit
    `Int.int` print its unsigned value, `pp_int` its signed value.  The
    symbol offsets (`ptrofs`, 32-bit on ARM) are reduced modulo `2^32`,
    since the port's `Ptrofs` is 64-bit.
  * `print_if` takes the destination file, the compile information and the
    atom properties as arguments (OCaml reads global references and `C2C`).
-/
import CCLib.arm.TargetPrinter
import CCLib.backend.JsonAST

namespace CC
namespace Arm
namespace AsmToJSON

open Asm Json

/-- `AsmToJSON.mnemonic_names` (`StringSet.elements`: sorted, without
    duplicates) -/
def mnemonicNames : List String :=
  (["Padc", "Padd", "Padds", "Pand", "Pannot", "Pasr", "Pb", "Pbc", "Pbic",
    "Pblreg", "Pblsymb", "Pbne", "Pbreg", "Pbsymb", "Pbtbl", "Pclz", "Pcmp",
    "Pcmn", "Pconstants", "Pfcpy_iif", "Pfcpy_fii", "Pfcpy_fi", "Pfcpy_sf",
    "Pflid_lbl", "Pflis_lbl", "Pdmb", "Pdsb", "Peor", "Pfabsd", "Pfabss",
    "Pfaddd", "Pfadds", "Pfcmpd", "Pfcmps", "Pfcmpzd", "Pfcmpzs", "Pfcpyd",
    "Pfcpy_fs", "Pfcpy_if", "Pfcvtds", "Pfcvtsd", "Pfdivd", "Pfdivs", "Pfldd",
    "Pflds", "Pflid_imm", "Pflis_imm", "Pfmuld", "Pfmuls", "Pfnegd",
    "Pfnegs", "Pfsitod", "Pfsitos", "Pfsqrt", "Pfstd", "Pfsts", "Pfsubd",
    "Pfsubs", "Pftosizd", "Pftosizs", "Pftouizd", "Pftouizs", "Pfuitod",
    "Pfuitos", "Pinlineasm", "Pisb", "Plabel", "Pldr", "Ploadsymbol_lbl",
    "Pldr_p", "Pldrb", "Pldrb_p", "Pldrh", "Pldrh_p", "Pldrsb", "Pldrsh",
    "Plsl", "Plsr", "Pmla", "Pmov", "Pmovite", "Pfmovite", "Pmovt", "Pmovw",
    "Pmul", "Pmvn", "Ploadsymbol_imm", "Pnop", "Porr", "Ppush", "Prev",
    "Prev16", "Prsb", "Prsbs", "Prsc", "Psbc", "Psbfx", "Psdiv", "Psmull",
    "Pstr", "Pstr_p", "Pstrb", "Pstrb_p", "Pstrh", "Pstrh_p", "Psub", "Psubs",
    "Pudiv", "Pumull"].mergeSort (fun a b => decide (a ≤ b))).eraseDups

/-- `AsmToJSON.instruction_arg` -/
inductive InstructionArg where
  | ALabel (l : Positive)
  | Atom (a : Positive)
  | Data32 (i : Integers.Int)
  | Data64 (i : Integers.Int64)
  | DFreg (r : Freg)
  | Float32 (f : Floats.Float32)
  | Float64 (f : Floats.Float)
  | Id
  | Ireg (r : Asm.Ireg)
  | Long (i : Integers.Int)
  | SFreg (r : Freg)
  | SPreg (r : Sreg)
  | Shift (so : ShiftOp)
  | String (s : _root_.String)
  | Symbol (id : Ident) (ofs : Integers.Ptrofs)
  | Condition (s : _root_.String)

/-- `AsmToJSON.makedata` -/
def makedata : CodeConstant → InstructionArg
  | .Float32 _ f => .Data32 (Floats.Float32.toBits f)
  | .Float64 _ f => .Data64 (Floats.Float.toBits f)
  | .Symbol _ id ofs => .Symbol id ofs

/-- `pp_int64` of a 32-bit integer: its unsigned value. -/
def ppUInt32 (i : Integers.Int) : M Unit := ppJint64 (Integers.Int.unsigned i)

/-- `AsmToJSON.pp_reg` -/
def ppReg (reg : _root_.String) : M Unit := ppJsingleObject "Register" ppJstring reg

/-- `AsmToJSON.pp_ireg` -/
def ppIreg (r : Asm.Ireg) : M Unit := ppReg (TargetPrinter.intRegName r)
/-- `AsmToJSON.pp_freg` -/
def ppFreg (r : Freg) : M Unit := ppReg (TargetPrinter.floatRegName r)
/-- `AsmToJSON.pp_single_freg` -/
def ppSingleFreg (r : Freg) : M Unit := ppReg (TargetPrinter.singleFloatRegName r)
/-- `AsmToJSON.pp_single_param_reg` -/
def ppSingleParamReg (r : Sreg) : M Unit := ppReg (TargetPrinter.singleParamRegName r)

/-- `AsmToJSON.pp_shiftreg` -/
def ppShiftreg (x : Asm.Ireg × _root_.String × Integers.Int) : M Unit := do
  let (r, op, n) := x
  ppJobjectStart
  ppJmember "Register" ppJstring (TargetPrinter.intRegName r) (first := true)
  ppJmember "Op" ppJstring op
  ppJmember "Amount" ppZ (Integers.Int.unsigned n)
  ppJobjectEnd

/-- `AsmToJSON.pp_shiftop` -/
def ppShiftop : ShiftOp → M Unit
  | .SOimm n => ppJsingleObject "Integer" ppUInt32 n
  | .SOreg r => ppIreg r
  | .SOlsl r n => ppJsingleObject "ShiftedRegister" ppShiftreg (r, "lsl", n)
  | .SOlsr r n => ppJsingleObject "ShiftedRegister" ppShiftreg (r, "lsr", n)
  | .SOasr r n => ppJsingleObject "ShiftedRegister" ppShiftreg (r, "asr", n)
  | .SOror r n => ppJsingleObject "ShiftedRegister" ppShiftreg (r, "ror", n)

/-- `AsmToJSON.pp_testcond` -/
def ppTestcond (bit : _root_.String) : M Unit := ppJsingleObject "Condition" ppJstring bit

/-- `AsmToJSON.pp_label` -/
def ppLabel (l : Positive) : M Unit := ppJsingleObject "Label" ppJint32 l.toNat

/-- `AsmToJSON.pp_symbol` -/
def ppSymbol (x : Ident × Integers.Ptrofs) : M Unit := do
  ppJobjectStart
  ppJmember "Name" ppAtom x.1 (first := true)
  ppJmember "Offset" ppZ (Integers.Ptrofs.unsigned x.2 % 2 ^ 32)
  ppJobjectEnd

/-- `AsmToJSON.pp_arg` -/
def ppArg : InstructionArg → M Unit
  | .ALabel lbl => ppLabel lbl
  | .Atom a => ppAtomConstant a
  | .Data32 i => ppJsingleObject "Data32" ppInt i
  | .Data64 i => ppJsingleObject "Data64" ppInt64 i
  | .DFreg fr => ppFreg fr
  | .Float32 f => ppFloat32Constant f
  | .Float64 f => ppFloat64Constant f
  | .Id => ppIdConst
  | .Ireg ir => ppIreg ir
  | .Long i => ppJsingleObject "Integer" ppUInt32 i
  | .SFreg fr => ppSingleFreg fr
  | .SPreg sr => ppSingleParamReg sr
  | .Shift so => ppShiftop so
  | .String s => ppJsingleObject "String" ppJstring s
  | .Symbol id ofs => ppJsingleObject "Symbol" ppSymbol (id, ofs)
  | .Condition b => ppTestcond b

/-- The JSON form of an annotation of kind 2 (`AisAnnot.json_ais_annot`
    with the registers of `TargetPrinter.preg_annot` and `r13`). -/
def jsonAnnot (txt : _root_.String) (args : List (BuiltinArg Preg)) : List AisAnnot.T :=
  match AisAnnot.jsonAisAnnot TargetPrinter.pregAnnot "r13" txt args with
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
  -- Should not occur (see the header)
  | .Pallocframe _ _ | .Pfreeframe _ _ | .Pcfi_adjust _ | .Pcfi_rel_offset _
  | .Pflis _ _ | .Pflid _ _ | .Ploadsymbol _ _ _ => pure ()
  -- ARM instructions
  | .Padc r1 r2 so => ppInstr "Padc" [.Ireg r1, .Ireg r2, .Shift so]
  | .Padd r1 r2 so => ppInstr "Padd" [.Ireg r1, .Ireg r2, .Shift so]
  | .Padds r1 r2 so => ppInstr "Padds" [.Ireg r1, .Ireg r2, .Shift so]
  | .Pand r1 r2 so => ppInstr "Pand" [.Ireg r1, .Ireg r2, .Shift so]
  | .Pasr r1 r2 r3 => ppInstr "Pasr" [.Ireg r1, .Ireg r2, .Ireg r3]
  | .Pb lbl => ppInstr "Pb" [.ALabel lbl]
  | .Pbc bit lbl => ppInstr "Pbc" [.Condition (TargetPrinter.conditionName bit), .ALabel lbl]
  | .Pbic r1 r2 so => ppInstr "Pbic" [.Ireg r1, .Ireg r2, .Shift so]
  | .Pblreg r _ => ppInstr "Pblreg" [.Ireg r]
  | .Pblsymb id _ => ppInstr "Pblsymb" [.Atom id]
  | .Pbne lbl => ppInstr "Pbne" [.ALabel lbl]
  | .Pbreg r _ => ppInstr "Pbreg" [.Ireg r]
  | .Pbsymb id _ => ppInstr "Pbsymb" [.Atom id]
  | .Pbtbl r tbl => ppInstr "Pbtbl" (.Ireg r :: tbl.map .ALabel)
  | .Pclz r1 r2 => ppInstr "Pclz" [.Ireg r1, .Ireg r2]
  | .Pcmp r1 so => ppInstr "Pcmp" [.Ireg r1, .Shift so]
  | .Pcmn r1 so => ppInstr "Pcmn" [.Ireg r1, .Shift so]
  | .Pdmb => ppInstr "Pdmb" []
  | .Pdsb => ppInstr "Pdsb" []
  | .Peor r1 r2 so => ppInstr "Peor" [.Ireg r1, .Ireg r2, .Shift so]
  | .Pfabsd r1 r2 => ppInstr "Pfabsd" [.DFreg r1, .DFreg r2]
  | .Pfabss r1 r2 => ppInstr "Pfabss" [.SFreg r1, .SFreg r2]
  | .Pfaddd r1 r2 r3 => ppInstr "Pfaddd" [.DFreg r1, .DFreg r2, .DFreg r3]
  | .Pfadds r1 r2 r3 => ppInstr "Pfadds" [.SFreg r1, .SFreg r2, .SFreg r3]
  | .Pfcmpd r1 r2 => ppInstr "Pfcmpd" [.DFreg r1, .DFreg r2]
  | .Pfcmps r1 r2 => ppInstr "Pfcmps" [.SFreg r1, .SFreg r2]
  | .Pfcmpzd r1 => ppInstr "Pfcmpzd" [.DFreg r1]
  | .Pfcmpzs r1 => ppInstr "Pfcmpzs" [.SFreg r1]
  | .Pfcpyd r1 r2 => ppInstr "Pfcpyd" [.DFreg r1, .DFreg r2]
  | .Pfcvtds r1 r2 => ppInstr "Pfcvtds" [.DFreg r1, .SFreg r2]
  | .Pfcvtsd r1 r2 => ppInstr "Pfcvtsd" [.SFreg r1, .DFreg r2]
  | .Pfdivd r1 r2 r3 => ppInstr "Pfdivd" [.DFreg r1, .DFreg r2, .DFreg r3]
  | .Pfdivs r1 r2 r3 => ppInstr "Pfdivs" [.SFreg r1, .SFreg r2, .SFreg r3]
  | .Pfldd r1 r2 n | .Pfldd_a r1 r2 n => ppInstr "Pfldd" [.DFreg r1, .Ireg r2, .Long n]
  | .Pflds r1 r2 n => ppInstr "Pflds" [.SFreg r1, .Ireg r2, .Long n]
  | .Pfmuld r1 r2 r3 => ppInstr "Pfmuld" [.DFreg r1, .DFreg r2, .DFreg r3]
  | .Pfmuls r1 r2 r3 => ppInstr "Pfmuls" [.SFreg r1, .SFreg r2, .SFreg r3]
  | .Pfnegd r1 r2 => ppInstr "Pfnegd" [.DFreg r1, .DFreg r2]
  | .Pfnegs r1 r2 => ppInstr "Pfnegs" [.SFreg r1, .SFreg r2]
  | .Pfsitod r1 r2 => ppInstr "Pfsitod" [.DFreg r1, .Ireg r2]
  | .Pfsitos r1 r2 => ppInstr "Pfsitos" [.SFreg r1, .Ireg r2]
  | .Pfsqrt r1 r2 => ppInstr "Pfsqrt" [.DFreg r1, .DFreg r2]
  | .Pfstd r1 r2 n | .Pfstd_a r1 r2 n => ppInstr "Pfstd" [.DFreg r1, .Ireg r2, .Long n]
  | .Pfsts r1 r2 n => ppInstr "Pfsts" [.SFreg r1, .Ireg r2, .Long n]
  | .Pfsubd r1 r2 r3 => ppInstr "Pfsubd" [.DFreg r1, .DFreg r2, .DFreg r3]
  | .Pfsubs r1 r2 r3 => ppInstr "Pfsubs" [.SFreg r1, .SFreg r2, .SFreg r3]
  | .Pftosizd r1 r2 => ppInstr "Pftosizd" [.Ireg r1, .DFreg r2]
  | .Pftosizs r1 r2 => ppInstr "Pftosizs" [.Ireg r1, .SFreg r2]
  | .Pftouizd r1 r2 => ppInstr "Pftouizd" [.Ireg r1, .DFreg r2]
  | .Pftouizs r1 r2 => ppInstr "Pftouizs" [.Ireg r1, .SFreg r2]
  | .Pfuitod r1 r2 => ppInstr "Pfuitod" [.DFreg r1, .Ireg r2]
  | .Pfuitos r1 r2 => ppInstr "Pfuitos" [.SFreg r1, .Ireg r2]
  | .Pisb => ppInstr "Pisb" []
  | .Plabel l => ppInstr "Plabel" [.ALabel l]
  | .Pldr r1 r2 so | .Pldr_a r1 r2 so => ppInstr "Pldr" [.Ireg r1, .Ireg r2, .Shift so]
  | .Pldr_p r1 r2 so => ppInstr "Pldr_p" [.Ireg r1, .Ireg r2, .Shift so]
  | .Pldrb r1 r2 so => ppInstr "Pldrb" [.Ireg r1, .Ireg r2, .Shift so]
  | .Pldrb_p r1 r2 so => ppInstr "Pldrb_p" [.Ireg r1, .Ireg r2, .Shift so]
  | .Pldrh r1 r2 so => ppInstr "Pldrh" [.Ireg r1, .Ireg r2, .Shift so]
  | .Pldrh_p r1 r2 so => ppInstr "Pldrh_p" [.Ireg r1, .Ireg r2, .Shift so]
  | .Pldrsb r1 r2 so => ppInstr "Pldrsb" [.Ireg r1, .Ireg r2, .Shift so]
  | .Pldrsh r1 r2 so => ppInstr "Pldrsh" [.Ireg r1, .Ireg r2, .Shift so]
  | .Plsl r1 r2 r3 => ppInstr "Plsl" [.Ireg r1, .Ireg r2, .Ireg r3]
  | .Plsr r1 r2 r3 => ppInstr "Plsr" [.Ireg r1, .Ireg r2, .Ireg r3]
  | .Pmla r1 r2 r3 r4 => ppInstr "Pmla" [.Ireg r1, .Ireg r2, .Ireg r3, .Ireg r4]
  | .Pmov r1 so => ppInstr "Pmov" [.Ireg r1, .Shift so]
  | .Pmovite cond r1 so1 so2 =>
    ppInstr "Pmovite" [.Ireg r1, .Condition (TargetPrinter.conditionName cond), .Shift so1,
      .Condition (TargetPrinter.negConditionName cond), .Shift so2]
  | .Pfmovite cond r1 r2 r3 =>
    ppInstr "Pfmovite" [.DFreg r1, .Condition (TargetPrinter.conditionName cond), .DFreg r2,
      .Condition (TargetPrinter.negConditionName cond), .DFreg r3]
  | .Pmovt r1 n => ppInstr "Pmovt" [.Ireg r1, .Long n]
  | .Pmovw r1 n => ppInstr "Pmovw" [.Ireg r1, .Long n]
  | .Pmul r1 r2 r3 => ppInstr "Pmul" [.Ireg r1, .Ireg r2, .Ireg r3]
  | .Pmvn r1 so => ppInstr "Pmvn" [.Ireg r1, .Shift so]
  | .Pnop => ppInstr "Pnop" []
  | .Porr r1 r2 so => ppInstr "Porr" [.Ireg r1, .Ireg r2, .Shift so]
  | .Ppush rl => ppInstr "Ppush" (rl.map .Ireg)
  | .Prev r1 r2 => ppInstr "Prev" [.Ireg r1, .Ireg r2]
  | .Prev16 r1 r2 => ppInstr "Prev16" [.Ireg r1, .Ireg r2]
  | .Prsb r1 r2 so => ppInstr "Prsb" [.Ireg r1, .Ireg r2, .Shift so]
  | .Prsbs r1 r2 so => ppInstr "Prsbs" [.Ireg r1, .Ireg r2, .Shift so]
  | .Prsc r1 r2 so => ppInstr "Prsc" [.Ireg r1, .Ireg r2, .Shift so]
  | .Psbc r1 r2 so => ppInstr "Psbc" [.Ireg r1, .Ireg r2, .Shift so]
  | .Psbfx r1 r2 lsb sz => ppInstr "Psbfx" [.Ireg r1, .Ireg r2, .Long lsb, .Long sz]
  | .Psdiv r1 r2 r3 => ppInstr "Psdiv" [.Ireg r1, .Ireg r2, .Ireg r3]
  | .Psmull r1 r2 r3 r4 => ppInstr "Psmull" [.Ireg r1, .Ireg r2, .Ireg r3, .Ireg r4]
  | .Pstr r1 r2 so | .Pstr_a r1 r2 so => ppInstr "Pstr" [.Ireg r1, .Ireg r2, .Shift so]
  | .Pstr_p r1 r2 so => ppInstr "Pstr_p" [.Ireg r1, .Ireg r2, .Shift so]
  | .Pstrb r1 r2 so => ppInstr "Pstrb" [.Ireg r1, .Ireg r2, .Shift so]
  | .Pstrb_p r1 r2 so => ppInstr "Pstrb_p" [.Ireg r1, .Ireg r2, .Shift so]
  | .Pstrh r1 r2 so => ppInstr "Pstrh" [.Ireg r1, .Ireg r2, .Shift so]
  | .Pstrh_p r1 r2 so => ppInstr "Pstrh_p" [.Ireg r1, .Ireg r2, .Shift so]
  | .Psub r1 r2 so => ppInstr "Psub" [.Ireg r1, .Ireg r2, .Shift so]
  | .Psubs r1 r2 so => ppInstr "Psubs" [.Ireg r1, .Ireg r2, .Shift so]
  | .Pudiv r1 r2 r3 => ppInstr "Pudiv" [.Ireg r1, .Ireg r2, .Ireg r3]
  | .Pumull r1 r2 r3 r4 => ppInstr "Pumull" [.Ireg r1, .Ireg r2, .Ireg r3, .Ireg r4]
  -- Fixup instructions for calling conventions
  | .Pfcpy_fs r1 r2 => ppInstr "Pfcpy_fs" [.SFreg r1, .SPreg r2]
  | .Pfcpy_sf r1 r2 => ppInstr "Pfcpy_sf" [.SPreg r1, .SFreg r2]
  | .Pfcpy_fii r1 r2 r3 => ppInstr "Pfcpy_fii" [.DFreg r1, .Ireg r2, .Ireg r3]
  | .Pfcpy_fi r1 r2 => ppInstr "Pfcpy_fi" [.SFreg r1, .Ireg r2]
  | .Pfcpy_iif r1 r2 r3 => ppInstr "Pfcpy_iif" [.Ireg r1, .Ireg r2, .DFreg r3]
  | .Pfcpy_if r1 r2 => ppInstr "Pfcpy_if" [.Ireg r1, .SFreg r2]
  -- Pseudo-instructions of the constant expansion
  | .Pconstants consts => ppInstr "Pconstants" (consts.map makedata)
  | .Ploadsymbol_imm r1 id ofs => ppInstr "Ploadsymbol_imm" [.Ireg r1, .Symbol id ofs]
  | .Pflid_lbl r1 lbl f => ppInstr "Pflid_lbl" [.DFreg r1, .ALabel lbl, .Float64 f]
  | .Pflis_lbl r1 lbl f => ppInstr "Pflis_lbl" [.SFreg r1, .ALabel lbl, .Float32 f]
  | .Pflid_imm r1 f => ppInstr "Pflid_imm" [.DFreg r1, .Float64 f]
  | .Pflis_imm r1 f => ppInstr "Pflis_imm" [.SFreg r1, .Float32 f]
  | .Ploadsymbol_lbl r1 lbl id ofs => ppInstr "Ploadsymbol_lbl" [.Ireg r1, .ALabel lbl, .Symbol id ofs]

/-- The instructions kept by `pp_instructions`: inline assembly, the
    annotations of kind 2 that have a JSON form, and every non-built-in
    instruction except the `.cfi` directives. -/
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
def printIf (destination : Option String) (sdumpFolder : String) (info : JsonAST.CompileInfo)
    (atoms : PrintAsm.AtomInfo) (isInline : Ident → Bool) (prog : Asm.Program)
    (sourcename : String) : IO Unit :=
  match destination with
  | none => pure ()
  | some f => do
    let f := if sdumpFolder.isEmpty then f else sdumpFolder ++ "/" ++ f
    IO.FS.writeFile f
      (render (JsonAST.ppAst info atoms isInline Asm.Function.fn_code ppInstructions prog sourcename))

/-- `AsmToJSON.pp_mnemonics` -/
def ppMnemonics : M Unit := JsonAST.ppMnemonics mnemonicNames

#guard render (ppInstructions [.Pmov .IR0 (.SOimm (Integers.Int.repr 1)), .Pcfi_adjust 0,
    .Pbreg .IR14 { sig_args := [], sig_res := .Xvoid, sig_cc := cc_default }]) =
  "[\n{ \"Instruction Name\" :\"Pmov\"\n, \"Args\" :[\n{ \"Register\" :\"r0\"\n}, " ++
  "\n{ \"Integer\" :1\n}]\n}, \n{ \"Instruction Name\" :\"Pbreg\"\n, \"Args\" :[\n{ \"Register\" :\"lr\"\n}]\n}]"
#guard mnemonicNames.length = 109 && mnemonicNames.head? = some "Padc"

end AsmToJSON
end Arm
end CC
