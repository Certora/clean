/-
  Abstract syntax and semantics for RISC-V assembly language — port of
  `riscV/Asm.v` (`fe_ofs_arg` comes from `CCLib.riscV.Stacklayout`).

  Ported: registers (`ireg`, `ireg0`, `freg`, `preg`), `offset`, the
  instruction set, `function`, `fundef`, `program`, register sets and their
  operations (`get0w`, `get0l`, `undef_regs`, `set_pair`, `set_regs`,
  `set_res`), `find_instr`, `is_label`, `label_pos`, `outcome`, `nextinstr`,
  `goto_label`, `eval_offset`, `exec_load`, `exec_store`, `eval_branch`,
  `exec_instr`, `preg_of`, `undef_caller_save_regs`, `extcall_arg`,
  `extcall_arg_pair`, `extcall_arguments`, `loc_external_result`, `state`,
  `step`, `initial_state`, `final_state`, `semantics`,
  `extcall_arguments_determ`, `data_preg`.

  Differences from Rocq:
  * The parameters `low_half`, `high_half` and the axiom `low_high_half`
    (how the linker splits `symbol + offset` into `%hi`/`%lo` parts) are the
    fields of a structure `HalfSplit` that the semantics takes as an
    argument, rather than global axioms.
  * The coercions `ireg >-> preg`, … are `Coe` instances; `Pregmap.t val` is
    the function type `Preg → Val`.
  * `semantics_determinate` is not ported (as for aarch64 and x86).
-/
import CCLib.backend.Mach
import CCLib.riscV.Op
import CCLib.riscV.Conventions
import CCLib.riscV.Stacklayout

namespace CC
namespace RiscV


namespace Asm

open Smallstep CC.RiscV.Conventions1

/-! ## Abstract syntax -/

/-- `Asm.ireg`: `x1`–`x31` (`x0` is `Ireg0.X0`). -/
inductive Ireg where
  | X1 | X2 | X3 | X4 | X5 | X6 | X7 | X8 | X9 | X10 | X11 | X12 | X13 | X14 | X15 | X16 | X17 | X18 | X19 | X20 | X21 | X22 | X23 | X24 | X25 | X26 | X27 | X28 | X29 | X30 | X31
  deriving DecidableEq, Repr

/-- `Asm.ireg0`: an integer register or the zero register `x0`. -/
inductive Ireg0 where
  | X0
  | X (r : Ireg)
  deriving DecidableEq, Repr

instance : Coe Ireg Ireg0 := ⟨.X⟩

/-- `Asm.freg` -/
inductive Freg where
  | F0 | F1 | F2 | F3 | F4 | F5 | F6 | F7 | F8 | F9 | F10 | F11 | F12 | F13 | F14 | F15 | F16 | F17 | F18 | F19 | F20 | F21 | F22 | F23 | F24 | F25 | F26 | F27 | F28 | F29 | F30 | F31
  deriving DecidableEq, Repr

/-- `Asm.preg` -/
inductive Preg where
  /-- integer registers -/
  | IR (r : Ireg)
  /-- double-precision float registers -/
  | FR (r : Freg)
  /-- program counter -/
  | PC
  deriving DecidableEq, Repr

instance : Coe Ireg Preg := ⟨.IR⟩
instance : Coe Freg Preg := ⟨.FR⟩

/-- The stack pointer `SP` = `X2`. -/
abbrev SP : Ireg := .X2
/-- The return-address register `RA` = `X1`. -/
abbrev RA : Ireg := .X1

/-- `Asm.offset`: an immediate or the low part of a symbol. -/
inductive Offset where
  | Ofsimm (ofs : Integers.Ptrofs)
  | Ofslow (id : Ident) (ofs : Integers.Ptrofs)
  deriving DecidableEq

/-- `Asm.label` -/
abbrev Label := Positive

/-- `Asm.instruction`.  The `W`-suffixed instructions operate on 32-bit
integers and the `L`-suffixed ones on 64-bit integers. -/
inductive Instruction where
  | Pmv (rd : Ireg) (rs : Ireg)
  | Pcsel (rd : Ireg) (rcond rs1 rs2 : Ireg)
  | Paddiw (rd : Ireg) (rs : Ireg0) (imm : Integers.Int)
  | Psltiw (rd : Ireg) (rs : Ireg0) (imm : Integers.Int)
  | Psltiuw (rd : Ireg) (rs : Ireg0) (imm : Integers.Int)
  | Pandiw (rd : Ireg) (rs : Ireg0) (imm : Integers.Int)
  | Poriw (rd : Ireg) (rs : Ireg0) (imm : Integers.Int)
  | Pxoriw (rd : Ireg) (rs : Ireg0) (imm : Integers.Int)
  | Pslliw (rd : Ireg) (rs : Ireg0) (imm : Integers.Int)
  | Psrliw (rd : Ireg) (rs : Ireg0) (imm : Integers.Int)
  | Psraiw (rd : Ireg) (rs : Ireg0) (imm : Integers.Int)
  | Pluiw (rd : Ireg) (imm : Integers.Int)
  | Paddw (rd : Ireg) (rs1 rs2 : Ireg0)
  | Psubw (rd : Ireg) (rs1 rs2 : Ireg0)
  | Pmulw (rd : Ireg) (rs1 rs2 : Ireg0)
  | Pmulhw (rd : Ireg) (rs1 rs2 : Ireg0)
  | Pmulhuw (rd : Ireg) (rs1 rs2 : Ireg0)
  | Pdivw (rd : Ireg) (rs1 rs2 : Ireg0)
  | Pdivuw (rd : Ireg) (rs1 rs2 : Ireg0)
  | Premw (rd : Ireg) (rs1 rs2 : Ireg0)
  | Premuw (rd : Ireg) (rs1 rs2 : Ireg0)
  | Psltw (rd : Ireg) (rs1 rs2 : Ireg0)
  | Psltuw (rd : Ireg) (rs1 rs2 : Ireg0)
  | Pseqw (rd : Ireg) (rs1 rs2 : Ireg0)
  | Psnew (rd : Ireg) (rs1 rs2 : Ireg0)
  | Pandw (rd : Ireg) (rs1 rs2 : Ireg0)
  | Porw (rd : Ireg) (rs1 rs2 : Ireg0)
  | Pxorw (rd : Ireg) (rs1 rs2 : Ireg0)
  | Psllw (rd : Ireg) (rs1 rs2 : Ireg0)
  | Psrlw (rd : Ireg) (rs1 rs2 : Ireg0)
  | Psraw (rd : Ireg) (rs1 rs2 : Ireg0)
  | Paddil (rd : Ireg) (rs : Ireg0) (imm : Integers.Int64)
  | Psltil (rd : Ireg) (rs : Ireg0) (imm : Integers.Int64)
  | Psltiul (rd : Ireg) (rs : Ireg0) (imm : Integers.Int64)
  | Pandil (rd : Ireg) (rs : Ireg0) (imm : Integers.Int64)
  | Poril (rd : Ireg) (rs : Ireg0) (imm : Integers.Int64)
  | Pxoril (rd : Ireg) (rs : Ireg0) (imm : Integers.Int64)
  | Psllil (rd : Ireg) (rs : Ireg0) (imm : Integers.Int)
  | Psrlil (rd : Ireg) (rs : Ireg0) (imm : Integers.Int)
  | Psrail (rd : Ireg) (rs : Ireg0) (imm : Integers.Int)
  | Pluil (rd : Ireg) (imm : Integers.Int64)
  | Paddl (rd : Ireg) (rs1 rs2 : Ireg0)
  | Psubl (rd : Ireg) (rs1 rs2 : Ireg0)
  | Pmull (rd : Ireg) (rs1 rs2 : Ireg0)
  | Pmulhl (rd : Ireg) (rs1 rs2 : Ireg0)
  | Pmulhul (rd : Ireg) (rs1 rs2 : Ireg0)
  | Pdivl (rd : Ireg) (rs1 rs2 : Ireg0)
  | Pdivul (rd : Ireg) (rs1 rs2 : Ireg0)
  | Preml (rd : Ireg) (rs1 rs2 : Ireg0)
  | Premul (rd : Ireg) (rs1 rs2 : Ireg0)
  | Psltl (rd : Ireg) (rs1 rs2 : Ireg0)
  | Psltul (rd : Ireg) (rs1 rs2 : Ireg0)
  | Pseql (rd : Ireg) (rs1 rs2 : Ireg0)
  | Psnel (rd : Ireg) (rs1 rs2 : Ireg0)
  | Pandl (rd : Ireg) (rs1 rs2 : Ireg0)
  | Porl (rd : Ireg) (rs1 rs2 : Ireg0)
  | Pxorl (rd : Ireg) (rs1 rs2 : Ireg0)
  | Pslll (rd : Ireg) (rs1 rs2 : Ireg0)
  | Psrll (rd : Ireg) (rs1 rs2 : Ireg0)
  | Psral (rd : Ireg) (rs1 rs2 : Ireg0)
  | Pcvtl2w (rd : Ireg) (rs : Ireg0)
  | Pcvtw2l (r : Ireg)
  | Pj_l (l : Label)
  | Pj_s (symb : Ident) (sg : Signature)
  | Pj_r (r : Ireg) (sg : Signature)
  | Pjal_s (symb : Ident) (sg : Signature)
  | Pjal_r (r : Ireg) (sg : Signature)
  | Pbeqw (rs1 rs2 : Ireg0) (l : Label)
  | Pbnew (rs1 rs2 : Ireg0) (l : Label)
  | Pbltw (rs1 rs2 : Ireg0) (l : Label)
  | Pbltuw (rs1 rs2 : Ireg0) (l : Label)
  | Pbgew (rs1 rs2 : Ireg0) (l : Label)
  | Pbgeuw (rs1 rs2 : Ireg0) (l : Label)
  | Pbeql (rs1 rs2 : Ireg0) (l : Label)
  | Pbnel (rs1 rs2 : Ireg0) (l : Label)
  | Pbltl (rs1 rs2 : Ireg0) (l : Label)
  | Pbltul (rs1 rs2 : Ireg0) (l : Label)
  | Pbgel (rs1 rs2 : Ireg0) (l : Label)
  | Pbgeul (rs1 rs2 : Ireg0) (l : Label)
  | Plb (rd : Ireg) (ra : Ireg) (ofs : Offset)
  | Plbu (rd : Ireg) (ra : Ireg) (ofs : Offset)
  | Plh (rd : Ireg) (ra : Ireg) (ofs : Offset)
  | Plhu (rd : Ireg) (ra : Ireg) (ofs : Offset)
  | Plw (rd : Ireg) (ra : Ireg) (ofs : Offset)
  | Plw_a (rd : Ireg) (ra : Ireg) (ofs : Offset)
  | Pld (rd : Ireg) (ra : Ireg) (ofs : Offset)
  | Pld_a (rd : Ireg) (ra : Ireg) (ofs : Offset)
  | Psb (rs : Ireg) (ra : Ireg) (ofs : Offset)
  | Psh (rs : Ireg) (ra : Ireg) (ofs : Offset)
  | Psw (rs : Ireg) (ra : Ireg) (ofs : Offset)
  | Psw_a (rs : Ireg) (ra : Ireg) (ofs : Offset)
  | Psd (rs : Ireg) (ra : Ireg) (ofs : Offset)
  | Psd_a (rs : Ireg) (ra : Ireg) (ofs : Offset)
  | Pfence
  | Pfmv (rd : Freg) (rs : Freg)
  | Pfmvxs (rd : Ireg) (rs : Freg)
  | Pfmvsx (rd : Freg) (rs : Ireg)
  | Pfmvxd (rd : Ireg) (rs : Freg)
  | Pfmvdx (rd : Freg) (rs : Ireg)
  | Pfls (rd : Freg) (ra : Ireg) (ofs : Offset)
  | Pfss (rs : Freg) (ra : Ireg) (ofs : Offset)
  | Pfnegs (rd : Freg) (rs : Freg)
  | Pfabss (rd : Freg) (rs : Freg)
  | Pfadds (rd : Freg) (rs1 rs2 : Freg)
  | Pfsubs (rd : Freg) (rs1 rs2 : Freg)
  | Pfmuls (rd : Freg) (rs1 rs2 : Freg)
  | Pfdivs (rd : Freg) (rs1 rs2 : Freg)
  | Pfmins (rd : Freg) (rs1 rs2 : Freg)
  | Pfmaxs (rd : Freg) (rs1 rs2 : Freg)
  | Pfeqs (rd : Ireg) (rs1 rs2 : Freg)
  | Pflts (rd : Ireg) (rs1 rs2 : Freg)
  | Pfles (rd : Ireg) (rs1 rs2 : Freg)
  | Pfsqrts (rd : Freg) (rs : Freg)
  | Pfmadds (rd : Freg) (rs1 rs2 rs3 : Freg)
  | Pfmsubs (rd : Freg) (rs1 rs2 rs3 : Freg)
  | Pfnmadds (rd : Freg) (rs1 rs2 rs3 : Freg)
  | Pfnmsubs (rd : Freg) (rs1 rs2 rs3 : Freg)
  | Pfcvtws (rd : Ireg) (rs : Freg)
  | Pfcvtwus (rd : Ireg) (rs : Freg)
  | Pfcvtsw (rd : Freg) (rs : Ireg0)
  | Pfcvtswu (rd : Freg) (rs : Ireg0)
  | Pfcvtls (rd : Ireg) (rs : Freg)
  | Pfcvtlus (rd : Ireg) (rs : Freg)
  | Pfcvtsl (rd : Freg) (rs : Ireg0)
  | Pfcvtslu (rd : Freg) (rs : Ireg0)
  | Pfld (rd : Freg) (ra : Ireg) (ofs : Offset)
  | Pfld_a (rd : Freg) (ra : Ireg) (ofs : Offset)
  | Pfsd (rd : Freg) (ra : Ireg) (ofs : Offset)
  | Pfsd_a (rd : Freg) (ra : Ireg) (ofs : Offset)
  | Pfnegd (rd : Freg) (rs : Freg)
  | Pfabsd (rd : Freg) (rs : Freg)
  | Pfaddd (rd : Freg) (rs1 rs2 : Freg)
  | Pfsubd (rd : Freg) (rs1 rs2 : Freg)
  | Pfmuld (rd : Freg) (rs1 rs2 : Freg)
  | Pfdivd (rd : Freg) (rs1 rs2 : Freg)
  | Pfmind (rd : Freg) (rs1 rs2 : Freg)
  | Pfmaxd (rd : Freg) (rs1 rs2 : Freg)
  | Pfeqd (rd : Ireg) (rs1 rs2 : Freg)
  | Pfltd (rd : Ireg) (rs1 rs2 : Freg)
  | Pfled (rd : Ireg) (rs1 rs2 : Freg)
  | Pfsqrtd (rd : Freg) (rs : Freg)
  | Pfmaddd (rd : Freg) (rs1 rs2 rs3 : Freg)
  | Pfmsubd (rd : Freg) (rs1 rs2 rs3 : Freg)
  | Pfnmaddd (rd : Freg) (rs1 rs2 rs3 : Freg)
  | Pfnmsubd (rd : Freg) (rs1 rs2 rs3 : Freg)
  | Pfcvtwd (rd : Ireg) (rs : Freg)
  | Pfcvtwud (rd : Ireg) (rs : Freg)
  | Pfcvtdw (rd : Freg) (rs : Ireg0)
  | Pfcvtdwu (rd : Freg) (rs : Ireg0)
  | Pfcvtld (rd : Ireg) (rs : Freg)
  | Pfcvtlud (rd : Ireg) (rs : Freg)
  | Pfcvtdl (rd : Freg) (rs : Ireg0)
  | Pfcvtdlu (rd : Freg) (rs : Ireg0)
  | Pfcvtds (rd : Freg) (rs : Freg)
  | Pfcvtsd (rd : Freg) (rs : Freg)
  | Pallocframe (sz : Z) (pos : Integers.Ptrofs)
  | Pfreeframe (sz : Z) (pos : Integers.Ptrofs)
  | Plabel (lbl : Label)
  | Ploadsymbol (rd : Ireg) (id : Ident) (ofs : Integers.Ptrofs)
  | Ploadsymbol_high (rd : Ireg) (id : Ident) (ofs : Integers.Ptrofs)
  | Ploadli (rd : Ireg) (i : Integers.Int64)
  | Ploadfi (rd : Freg) (f : Floats.Float)
  | Ploadsi (rd : Freg) (f : Floats.Float32)
  | Pbtbl (r : Ireg) (tbl : List Label)
  | Pbuiltin (ef : ExtFun) (args : List (BuiltinArg Preg)) (res : BuiltinRes Preg)
  | Pnop
  | Pcfi_rel_offset (ofs : Integers.Int)
  | Pcfi_adjust (ofs : Integers.Int)

/-- `Asm.code` -/
abbrev Code := List Instruction

/-- `Asm.function` -/
structure Function where
  fn_sig : Signature
  fn_code : Code

/-- `Asm.fundef` -/
abbrev Fundef := ASTFundef Function
/-- `Asm.program` -/
abbrev Program := ASTProgram Fundef Unit

/-! ## Operational semantics -/

/-- `Asm.regset` (`Pregmap.t val`) -/
abbrev Regset := Preg → Val
/-- `Asm.genv` -/
abbrev CGenv := Genv Fundef Unit

/-- `Pregmap.set` (`rs # r <- v`) -/
def Regset.set (rs : Regset) (r : Preg) (v : Val) : Regset :=
  fun r' => if r' = r then v else rs r'

/-- `Pregmap.init` -/
def Regset.init (v : Val) : Regset := fun _ => v

/-- `Asm.get0w` (`rs ## r`): `x0` reads as the 32-bit zero. -/
def get0w (rs : Regset) : Ireg0 → Val
  | .X0 => .Vint Integers.Int.zero
  | .X r => rs (.IR r)

/-- `Asm.get0l` (`rs ### r`): `x0` reads as the 64-bit zero. -/
def get0l (rs : Regset) : Ireg0 → Val
  | .X0 => .Vlong Integers.Int64.zero
  | .X r => rs (.IR r)

/-- `Asm.undef_regs` -/
def undefRegs : List Preg → Regset → Regset
  | [], rs => rs
  | r :: l', rs => undefRegs l' (rs.set r .Vundef)

/-- `Asm.set_pair` -/
def setPair (p : RPair Preg) (v : Val) (rs : Regset) : Regset :=
  match p with
  | .One r => rs.set r v
  | .Twolong rhi rlo => (rs.set rhi (Val.hiword v)).set rlo (Val.loword v)

/-- `Asm.set_regs` -/
def setRegs : List Preg → List Val → Regset → Regset
  | r1 :: rl', v1 :: vl', rs => setRegs rl' vl' (rs.set r1 v1)
  | _, _, rs => rs

/-- `Asm.set_res` -/
def setRes : BuiltinRes Preg → Val → Regset → Regset
  | .BR r, v, rs => rs.set r v
  | .BR_none, _, rs => rs
  | .BR_splitlong hi lo, v, rs => setRes lo (Val.loword v) (setRes hi (Val.hiword v) rs)

/-- `Asm.find_instr` -/
def findInstr (pos : Z) : Code → Option Instruction
  | [] => none
  | i :: il => if pos = 0 then some i else findInstr (pos - 1) il

/-- `Asm.is_label` -/
def isLabel (lbl : Label) (instr : Instruction) : Bool :=
  match instr with
  | .Plabel lbl' => decide (lbl = lbl')
  | _ => false

/-- `Asm.is_label_correct` -/
theorem isLabel_correct (lbl : Label) (instr : Instruction) :
    if isLabel lbl instr then instr = .Plabel lbl else instr ≠ .Plabel lbl := by
  cases instr <;> simp [isLabel]
  case Plabel l => by_cases h : lbl = l <;> simp [h, eq_comm]

/-- `Asm.label_pos` -/
def labelPos (lbl : Label) (pos : Z) : Code → Option Z
  | [] => none
  | instr :: c' => if isLabel lbl instr then some (pos + 1) else labelPos lbl (pos + 1) c'

/-- The parameters `Asm.low_half`, `Asm.high_half` and the axiom
`Asm.low_high_half`: how the linker splits the address `symbol + offset`
into a 20-bit high part and a 12-bit low part. -/
structure HalfSplit where
  low_half : CGenv → Ident → Integers.Ptrofs → Integers.Ptrofs
  high_half : CGenv → Ident → Integers.Ptrofs → Val
  low_high_half : ∀ ge id ofs,
    Val.offsetPtr (high_half ge id ofs) (low_half ge id ofs) = Genv.symbolAddress ge id ofs

/-- `Asm.outcome` -/
inductive Outcome where
  | Next (rs : Regset) (m : Mem)
  | Stuck

/-- `Asm.nextinstr` -/
def nextinstr (rs : Regset) : Regset :=
  rs.set .PC (Val.offsetPtr (rs .PC) Integers.Ptrofs.one)

/-- `Asm.goto_label` -/
def gotoLabel (f : Function) (lbl : Label) (rs : Regset) (m : Mem) : Outcome :=
  match labelPos lbl 0 f.fn_code with
  | none => .Stuck
  | some pos =>
      match rs .PC with
      | .Vptr b _ => .Next (rs.set .PC (.Vptr b (Integers.Ptrofs.repr pos))) m
      | _ => .Stuck

/-- `Asm.eval_branch` -/
def evalBranch (f : Function) (l : Label) (rs : Regset) (m : Mem) (res : Option Bool) :
    Outcome :=
  match res with
  | some true => gotoLabel f l rs m
  | some false => .Next (nextinstr rs) m
  | none => .Stuck

/-- `Next (nextinstr (rs # rd <- v)) m` -/
abbrev nextSet (rs : Regset) (rd : Preg) (v : Val) (m : Mem) : Outcome :=
  .Next (nextinstr (rs.set rd v)) m

section RELSEM
variable (sym : HalfSplit) (ge : CGenv)

/-- `Asm.eval_offset` -/
def evalOffset (ofs : Offset) : Integers.Ptrofs :=
  match ofs with
  | .Ofsimm n => n
  | .Ofslow id delta => sym.low_half ge id delta

/-- `Asm.exec_load` -/
def execLoad (chunk : Chunk) (rs : Regset) (m : Mem) (d : Preg) (a : Ireg) (ofs : Offset) :
    Outcome :=
  match Mem.loadv chunk m (Val.offsetPtr (rs (.IR a)) (evalOffset sym ge ofs)) with
  | none => .Stuck
  | some v => .Next (nextinstr (rs.set d v)) m

/-- `Asm.exec_store` -/
def execStore (chunk : Chunk) (rs : Regset) (m : Mem) (s : Preg) (a : Ireg) (ofs : Offset) :
    Outcome :=
  match Mem.storev chunk m (Val.offsetPtr (rs (.IR a)) (evalOffset sym ge ofs)) (rs s) with
  | none => .Stuck
  | some m' => .Next (nextinstr rs) m'

/-- `Asm.exec_instr`.  Registers used as temporaries by the expansion of
pseudo-instructions (`X31`, and `X6` for jump tables) are set to `Vundef`. -/
def execInstr (f : Function) (i : Instruction) (rs : Regset) (m : Mem) : Outcome :=
  match i with
  | .Pmv d s => nextSet rs d ((rs s)) m
  | .Paddiw d s i => nextSet rs d (Val.add (get0w rs s) (.Vint i)) m
  | .Psltiw d s i => nextSet rs d (Val.cmp .Clt (get0w rs s) (.Vint i)) m
  | .Psltiuw d s i => nextSet rs d (Val.cmpu (Mem.validPointer m) .Clt (get0w rs s) (.Vint i)) m
  | .Pandiw d s i => nextSet rs d (Val.and (get0w rs s) (.Vint i)) m
  | .Poriw d s i => nextSet rs d (Val.or (get0w rs s) (.Vint i)) m
  | .Pxoriw d s i => nextSet rs d (Val.xor (get0w rs s) (.Vint i)) m
  | .Pslliw d s i => nextSet rs d (Val.shl (get0w rs s) (.Vint i)) m
  | .Psrliw d s i => nextSet rs d (Val.shru (get0w rs s) (.Vint i)) m
  | .Psraiw d s i => nextSet rs d (Val.shr (get0w rs s) (.Vint i)) m
  | .Pluiw d i => nextSet rs d (.Vint (Integers.Int.shl i (Integers.Int.repr 12))) m
  | .Paddw d s1 s2 => nextSet rs d (Val.add (get0w rs s1) (get0w rs s2)) m
  | .Psubw d s1 s2 => nextSet rs d (Val.sub (get0w rs s1) (get0w rs s2)) m
  | .Pmulw d s1 s2 => nextSet rs d (Val.mul (get0w rs s1) (get0w rs s2)) m
  | .Pmulhw d s1 s2 => nextSet rs d (Val.mulhs (get0w rs s1) (get0w rs s2)) m
  | .Pmulhuw d s1 s2 => nextSet rs d (Val.mulhu (get0w rs s1) (get0w rs s2)) m
  | .Pdivw d s1 s2 => nextSet rs d (Val.maketotal (Val.divs (get0w rs s1) (get0w rs s2))) m
  | .Pdivuw d s1 s2 => nextSet rs d (Val.maketotal (Val.divu (get0w rs s1) (get0w rs s2))) m
  | .Premw d s1 s2 => nextSet rs d (Val.maketotal (Val.mods (get0w rs s1) (get0w rs s2))) m
  | .Premuw d s1 s2 => nextSet rs d (Val.maketotal (Val.modu (get0w rs s1) (get0w rs s2))) m
  | .Psltw d s1 s2 => nextSet rs d (Val.cmp .Clt (get0w rs s1) (get0w rs s2)) m
  | .Psltuw d s1 s2 => nextSet rs d (Val.cmpu (Mem.validPointer m) .Clt (get0w rs s1) (get0w rs s2)) m
  | .Pseqw d s1 s2 => nextSet rs d (Val.cmpu (Mem.validPointer m) .Ceq (get0w rs s1) (get0w rs s2)) m
  | .Psnew d s1 s2 => nextSet rs d (Val.cmpu (Mem.validPointer m) .Cne (get0w rs s1) (get0w rs s2)) m
  | .Pandw d s1 s2 => nextSet rs d (Val.and (get0w rs s1) (get0w rs s2)) m
  | .Porw d s1 s2 => nextSet rs d (Val.or (get0w rs s1) (get0w rs s2)) m
  | .Pxorw d s1 s2 => nextSet rs d (Val.xor (get0w rs s1) (get0w rs s2)) m
  | .Psllw d s1 s2 => nextSet rs d (Val.shl (get0w rs s1) (get0w rs s2)) m
  | .Psrlw d s1 s2 => nextSet rs d (Val.shru (get0w rs s1) (get0w rs s2)) m
  | .Psraw d s1 s2 => nextSet rs d (Val.shr (get0w rs s1) (get0w rs s2)) m
  | .Paddil d s i => nextSet rs d (Val.addl (get0l rs s) (.Vlong i)) m
  | .Psltil d s i => nextSet rs d (Val.maketotal (Val.cmpl .Clt (get0l rs s) (.Vlong i))) m
  | .Psltiul d s i => nextSet rs d (Val.maketotal (Val.cmplu (Mem.validPointer m) .Clt (get0l rs s) (.Vlong i))) m
  | .Pandil d s i => nextSet rs d (Val.andl (get0l rs s) (.Vlong i)) m
  | .Poril d s i => nextSet rs d (Val.orl (get0l rs s) (.Vlong i)) m
  | .Pxoril d s i => nextSet rs d (Val.xorl (get0l rs s) (.Vlong i)) m
  | .Psllil d s i => nextSet rs d (Val.shll (get0l rs s) (.Vint i)) m
  | .Psrlil d s i => nextSet rs d (Val.shrlu (get0l rs s) (.Vint i)) m
  | .Psrail d s i => nextSet rs d (Val.shrl (get0l rs s) (.Vint i)) m
  | .Pluil d i => nextSet rs d (.Vlong (Integers.Int64.sign_ext 32 (Integers.Int64.shl i (Integers.Int64.repr 12)))) m
  | .Paddl d s1 s2 => nextSet rs d (Val.addl (get0l rs s1) (get0l rs s2)) m
  | .Psubl d s1 s2 => nextSet rs d (Val.subl (get0l rs s1) (get0l rs s2)) m
  | .Pmull d s1 s2 => nextSet rs d (Val.mull (get0l rs s1) (get0l rs s2)) m
  | .Pmulhl d s1 s2 => nextSet rs d (Val.mullhs (get0l rs s1) (get0l rs s2)) m
  | .Pmulhul d s1 s2 => nextSet rs d (Val.mullhu (get0l rs s1) (get0l rs s2)) m
  | .Pdivl d s1 s2 => nextSet rs d (Val.maketotal (Val.divls (get0l rs s1) (get0l rs s2))) m
  | .Pdivul d s1 s2 => nextSet rs d (Val.maketotal (Val.divlu (get0l rs s1) (get0l rs s2))) m
  | .Preml d s1 s2 => nextSet rs d (Val.maketotal (Val.modls (get0l rs s1) (get0l rs s2))) m
  | .Premul d s1 s2 => nextSet rs d (Val.maketotal (Val.modlu (get0l rs s1) (get0l rs s2))) m
  | .Psltl d s1 s2 => nextSet rs d (Val.maketotal (Val.cmpl .Clt (get0l rs s1) (get0l rs s2))) m
  | .Psltul d s1 s2 => nextSet rs d (Val.maketotal (Val.cmplu (Mem.validPointer m) .Clt (get0l rs s1) (get0l rs s2))) m
  | .Pseql d s1 s2 => nextSet rs d (Val.maketotal (Val.cmplu (Mem.validPointer m) .Ceq (get0l rs s1) (get0l rs s2))) m
  | .Psnel d s1 s2 => nextSet rs d (Val.maketotal (Val.cmplu (Mem.validPointer m) .Cne (get0l rs s1) (get0l rs s2))) m
  | .Pandl d s1 s2 => nextSet rs d (Val.andl (get0l rs s1) (get0l rs s2)) m
  | .Porl d s1 s2 => nextSet rs d (Val.orl (get0l rs s1) (get0l rs s2)) m
  | .Pxorl d s1 s2 => nextSet rs d (Val.xorl (get0l rs s1) (get0l rs s2)) m
  | .Pslll d s1 s2 => nextSet rs d (Val.shll (get0l rs s1) (get0l rs s2)) m
  | .Psrll d s1 s2 => nextSet rs d (Val.shrlu (get0l rs s1) (get0l rs s2)) m
  | .Psral d s1 s2 => nextSet rs d (Val.shrl (get0l rs s1) (get0l rs s2)) m
  | .Pcvtl2w d s => nextSet rs d (Val.loword (get0w rs s)) m
  | .Pbeqw s1 s2 l => evalBranch f l rs m (Val.cmpu_bool (Mem.validPointer m) .Ceq (get0w rs s1) (get0w rs s2))
  | .Pbnew s1 s2 l => evalBranch f l rs m (Val.cmpu_bool (Mem.validPointer m) .Cne (get0w rs s1) (get0w rs s2))
  | .Pbltw s1 s2 l => evalBranch f l rs m (Val.cmp_bool .Clt (get0w rs s1) (get0w rs s2))
  | .Pbltuw s1 s2 l => evalBranch f l rs m (Val.cmpu_bool (Mem.validPointer m) .Clt (get0w rs s1) (get0w rs s2))
  | .Pbgew s1 s2 l => evalBranch f l rs m (Val.cmp_bool .Cge (get0w rs s1) (get0w rs s2))
  | .Pbgeuw s1 s2 l => evalBranch f l rs m (Val.cmpu_bool (Mem.validPointer m) .Cge (get0w rs s1) (get0w rs s2))
  | .Pbeql s1 s2 l => evalBranch f l rs m (Val.cmplu_bool (Mem.validPointer m) .Ceq (get0l rs s1) (get0l rs s2))
  | .Pbnel s1 s2 l => evalBranch f l rs m (Val.cmplu_bool (Mem.validPointer m) .Cne (get0l rs s1) (get0l rs s2))
  | .Pbltl s1 s2 l => evalBranch f l rs m (Val.cmpl_bool .Clt (get0l rs s1) (get0l rs s2))
  | .Pbltul s1 s2 l => evalBranch f l rs m (Val.cmplu_bool (Mem.validPointer m) .Clt (get0l rs s1) (get0l rs s2))
  | .Pbgel s1 s2 l => evalBranch f l rs m (Val.cmpl_bool .Cge (get0l rs s1) (get0l rs s2))
  | .Pbgeul s1 s2 l => evalBranch f l rs m (Val.cmplu_bool (Mem.validPointer m) .Cge (get0l rs s1) (get0l rs s2))
  | .Plb d a ofs => execLoad sym ge .Mint8signed rs m d a ofs
  | .Plbu d a ofs => execLoad sym ge .Mint8unsigned rs m d a ofs
  | .Plh d a ofs => execLoad sym ge .Mint16signed rs m d a ofs
  | .Plhu d a ofs => execLoad sym ge .Mint16unsigned rs m d a ofs
  | .Plw d a ofs => execLoad sym ge .Mint32 rs m d a ofs
  | .Plw_a d a ofs => execLoad sym ge .Many32 rs m d a ofs
  | .Pld d a ofs => execLoad sym ge .Mint64 rs m d a ofs
  | .Pld_a d a ofs => execLoad sym ge .Many64 rs m d a ofs
  | .Psb s a ofs => execStore sym ge .Mint8unsigned rs m s a ofs
  | .Psh s a ofs => execStore sym ge .Mint16unsigned rs m s a ofs
  | .Psw s a ofs => execStore sym ge .Mint32 rs m s a ofs
  | .Psw_a s a ofs => execStore sym ge .Many32 rs m s a ofs
  | .Psd s a ofs => execStore sym ge .Mint64 rs m s a ofs
  | .Psd_a s a ofs => execStore sym ge .Many64 rs m s a ofs
  | .Pfmv d s => nextSet rs d ((rs s)) m
  | .Pfls d a ofs => execLoad sym ge .Mfloat32 rs m d a ofs
  | .Pfss s a ofs => execStore sym ge .Mfloat32 rs m s a ofs
  | .Pfnegs d s => nextSet rs d (Val.negfs (rs s)) m
  | .Pfabss d s => nextSet rs d (Val.absfs (rs s)) m
  | .Pfadds d s1 s2 => nextSet rs d (Val.addfs (rs s1) (rs s2)) m
  | .Pfsubs d s1 s2 => nextSet rs d (Val.subfs (rs s1) (rs s2)) m
  | .Pfmuls d s1 s2 => nextSet rs d (Val.mulfs (rs s1) (rs s2)) m
  | .Pfdivs d s1 s2 => nextSet rs d (Val.divfs (rs s1) (rs s2)) m
  | .Pfeqs d s1 s2 => nextSet rs d (Val.cmpfs .Ceq (rs s1) (rs s2)) m
  | .Pflts d s1 s2 => nextSet rs d (Val.cmpfs .Clt (rs s1) (rs s2)) m
  | .Pfles d s1 s2 => nextSet rs d (Val.cmpfs .Cle (rs s1) (rs s2)) m
  | .Pfcvtws d s => nextSet rs d (Val.maketotal (Val.intofsingle (rs s))) m
  | .Pfcvtwus d s => nextSet rs d (Val.maketotal (Val.intuofsingle (rs s))) m
  | .Pfcvtsw d s => nextSet rs d (Val.maketotal (Val.singleofint (get0w rs s))) m
  | .Pfcvtswu d s => nextSet rs d (Val.maketotal (Val.singleofintu (get0w rs s))) m
  | .Pfcvtls d s => nextSet rs d (Val.maketotal (Val.longofsingle (rs s))) m
  | .Pfcvtlus d s => nextSet rs d (Val.maketotal (Val.longuofsingle (rs s))) m
  | .Pfcvtsl d s => nextSet rs d (Val.maketotal (Val.singleoflong (get0l rs s))) m
  | .Pfcvtslu d s => nextSet rs d (Val.maketotal (Val.singleoflongu (get0l rs s))) m
  | .Pfld d a ofs => execLoad sym ge .Mfloat64 rs m d a ofs
  | .Pfld_a d a ofs => execLoad sym ge .Many64 rs m d a ofs
  | .Pfsd s a ofs => execStore sym ge .Mfloat64 rs m s a ofs
  | .Pfsd_a s a ofs => execStore sym ge .Many64 rs m s a ofs
  | .Pfnegd d s => nextSet rs d (Val.negf (rs s)) m
  | .Pfabsd d s => nextSet rs d (Val.absf (rs s)) m
  | .Pfaddd d s1 s2 => nextSet rs d (Val.addf (rs s1) (rs s2)) m
  | .Pfsubd d s1 s2 => nextSet rs d (Val.subf (rs s1) (rs s2)) m
  | .Pfmuld d s1 s2 => nextSet rs d (Val.mulf (rs s1) (rs s2)) m
  | .Pfdivd d s1 s2 => nextSet rs d (Val.divf (rs s1) (rs s2)) m
  | .Pfeqd d s1 s2 => nextSet rs d (Val.cmpf .Ceq (rs s1) (rs s2)) m
  | .Pfltd d s1 s2 => nextSet rs d (Val.cmpf .Clt (rs s1) (rs s2)) m
  | .Pfled d s1 s2 => nextSet rs d (Val.cmpf .Cle (rs s1) (rs s2)) m
  | .Pfcvtwd d s => nextSet rs d (Val.maketotal (Val.intoffloat (rs s))) m
  | .Pfcvtwud d s => nextSet rs d (Val.maketotal (Val.intuoffloat (rs s))) m
  | .Pfcvtdw d s => nextSet rs d (Val.maketotal (Val.floatofint (get0w rs s))) m
  | .Pfcvtdwu d s => nextSet rs d (Val.maketotal (Val.floatofintu (get0w rs s))) m
  | .Pfcvtld d s => nextSet rs d (Val.maketotal (Val.longoffloat (rs s))) m
  | .Pfcvtlud d s => nextSet rs d (Val.maketotal (Val.longuoffloat (rs s))) m
  | .Pfcvtdl d s => nextSet rs d (Val.maketotal (Val.floatoflong (get0l rs s))) m
  | .Pfcvtdlu d s => nextSet rs d (Val.maketotal (Val.floatoflongu (get0l rs s))) m
  | .Pfcvtds d s => nextSet rs d (Val.floatofsingle (rs s)) m
  | .Pfcvtsd d s => nextSet rs d (Val.singleoffloat (rs s)) m
  | .Pcsel d c s1 s2 =>
      let v :=
        if rs (.IR c) = Val.Vone then rs (.IR s1) else
        if rs (.IR c) = Val.Vzero then rs (.IR s2) else .Vundef
      .Next (nextinstr ((rs.set d v).set (.IR .X31) .Vundef)) m
  | .Pcvtw2l r => nextSet rs r (Val.longofint (rs (.IR r))) m
  | .Pj_l l => gotoLabel f l rs m
  | .Pj_s s _ =>
      .Next ((rs.set .PC (Genv.symbolAddress ge s Integers.Ptrofs.zero)).set (.IR .X31) .Vundef) m
  | .Pj_r r _ => .Next (rs.set .PC (rs (.IR r))) m
  | .Pjal_s s _ =>
      .Next ((rs.set .PC (Genv.symbolAddress ge s Integers.Ptrofs.zero)).set (.IR RA)
        (Val.offsetPtr (rs .PC) Integers.Ptrofs.one)) m
  | .Pjal_r r _ =>
      .Next ((rs.set .PC (rs (.IR r))).set (.IR RA)
        (Val.offsetPtr (rs .PC) Integers.Ptrofs.one)) m
  | .Pallocframe sz pos =>
      let (m1, stk) := Mem.alloc m 0 sz
      let sp : Val := .Vptr stk Integers.Ptrofs.zero
      match Mem.storev Mptr m1 (Val.offsetPtr sp pos) (rs (.IR SP)) with
      | none => .Stuck
      | some m2 =>
          .Next (nextinstr (((rs.set (.IR .X30) (rs (.IR SP))).set (.IR SP) sp).set
            (.IR .X31) .Vundef)) m2
  | .Pfreeframe sz pos =>
      match Mem.loadv Mptr m (Val.offsetPtr (rs (.IR SP)) pos) with
      | none => .Stuck
      | some v =>
          match rs (.IR SP) with
          | .Vptr stk _ =>
              match Mem.free m stk 0 sz with
              | none => .Stuck
              | some m' => .Next (nextinstr ((rs.set (.IR SP) v).set (.IR .X31) .Vundef)) m'
          | _ => .Stuck
  | .Plabel _ => .Next (nextinstr rs) m
  | .Ploadsymbol rd s ofs => nextSet rs rd (Genv.symbolAddress ge s ofs) m
  | .Ploadsymbol_high rd s ofs => nextSet rs rd (sym.high_half ge s ofs) m
  | .Ploadli rd i => .Next (nextinstr ((rs.set (.IR .X31) .Vundef).set rd (.Vlong i))) m
  | .Ploadfi rd f => .Next (nextinstr ((rs.set (.IR .X31) .Vundef).set rd (.Vfloat f))) m
  | .Ploadsi rd f => .Next (nextinstr ((rs.set (.IR .X31) .Vundef).set rd (.Vsingle f))) m
  | .Pbtbl r tbl =>
      match rs (.IR r) with
      | .Vint n =>
          match CminorSel.listNthZ tbl (Integers.Int.unsigned n) with
          | none => .Stuck
          | some lbl => gotoLabel f lbl ((rs.set (.IR .X6) .Vundef).set (.IR .X31) .Vundef) m
      | _ => .Stuck
  | .Pcfi_rel_offset _ => .Next (nextinstr rs) m
  -- treated specially by `step`
  | .Pbuiltin .. => .Stuck
  -- not generated by `Asmgen`, hence not modelled
  | .Pfence
  | .Pfmvxs ..
  | .Pfmvsx ..
  | .Pfmvxd ..
  | .Pfmvdx ..
  | .Pfmins ..
  | .Pfmaxs ..
  | .Pfsqrts ..
  | .Pfmadds ..
  | .Pfmsubs ..
  | .Pfnmadds ..
  | .Pfnmsubs ..
  | .Pfmind ..
  | .Pfmaxd ..
  | .Pfsqrtd ..
  | .Pfmaddd ..
  | .Pfmsubd ..
  | .Pfnmaddd ..
  | .Pfnmsubd ..
  | .Pnop
  | .Pcfi_adjust .. => .Stuck

end RELSEM

/-- `Asm.preg_of`: the Asm view of a machine register (no machine register
maps to the temporary `X31`). -/
def pregOf (r : Mreg) : Preg :=
  match r with
  | .R5 => .IR .X5
  | .R6 => .IR .X6
  | .R7 => .IR .X7
  | .R8 => .IR .X8
  | .R9 => .IR .X9
  | .R10 => .IR .X10
  | .R11 => .IR .X11
  | .R12 => .IR .X12
  | .R13 => .IR .X13
  | .R14 => .IR .X14
  | .R15 => .IR .X15
  | .R16 => .IR .X16
  | .R17 => .IR .X17
  | .R18 => .IR .X18
  | .R19 => .IR .X19
  | .R20 => .IR .X20
  | .R21 => .IR .X21
  | .R22 => .IR .X22
  | .R23 => .IR .X23
  | .R24 => .IR .X24
  | .R25 => .IR .X25
  | .R26 => .IR .X26
  | .R27 => .IR .X27
  | .R28 => .IR .X28
  | .R29 => .IR .X29
  | .R30 => .IR .X30
  | .F0 => .FR .F0
  | .F1 => .FR .F1
  | .F2 => .FR .F2
  | .F3 => .FR .F3
  | .F4 => .FR .F4
  | .F5 => .FR .F5
  | .F6 => .FR .F6
  | .F7 => .FR .F7
  | .F8 => .FR .F8
  | .F9 => .FR .F9
  | .F10 => .FR .F10
  | .F11 => .FR .F11
  | .F12 => .FR .F12
  | .F13 => .FR .F13
  | .F14 => .FR .F14
  | .F15 => .FR .F15
  | .F16 => .FR .F16
  | .F17 => .FR .F17
  | .F18 => .FR .F18
  | .F19 => .FR .F19
  | .F20 => .FR .F20
  | .F21 => .FR .F21
  | .F22 => .FR .F22
  | .F23 => .FR .F23
  | .F24 => .FR .F24
  | .F25 => .FR .F25
  | .F26 => .FR .F26
  | .F27 => .FR .F27
  | .F28 => .FR .F28
  | .F29 => .FR .F29
  | .F30 => .FR .F30
  | .F31 => .FR .F31

/-- `Asm.undef_caller_save_regs`: undefine all registers except `SP` and the
callee-save registers. -/
def undefCallerSaveRegs (rs : Regset) : Regset := fun r =>
  if decide (r = .IR SP) ||
     decide (r ∈ ((Mreg.allMregs.filter isCalleeSave).map pregOf)) then rs r
  else .Vundef

/-- `Asm.extcall_arg` -/
inductive ExtcallArg (rs : Regset) (m : Mem) : Loc → Val → Prop where
  | reg (r) : ExtcallArg rs m (.R r) (rs (pregOf r))
  | stack (ofs ty bofs v) :
      bofs = Stacklayout.feOfsArg + 4 * ofs →
      Mem.loadv (Chunk.ofTyp ty) m
        (Val.offsetPtr (rs (.IR SP)) (Integers.Ptrofs.repr bofs)) = some v →
      ExtcallArg rs m (.S .Outgoing ofs ty) v

/-- `Asm.extcall_arg_pair` -/
inductive ExtcallArgPair (rs : Regset) (m : Mem) : RPair Loc → Val → Prop where
  | one (l v) : ExtcallArg rs m l v → ExtcallArgPair rs m (.One l) v
  | twolong (hi lo vhi vlo) :
      ExtcallArg rs m hi vhi → ExtcallArg rs m lo vlo →
      ExtcallArgPair rs m (.Twolong hi lo) (Val.longofwords vhi vlo)

/-- `Asm.extcall_arguments` -/
def ExtcallArguments (rs : Regset) (m : Mem) (sg : Signature) (args : List Val) : Prop :=
  ListForall2 (ExtcallArgPair rs m) (locArguments sg) args

/-- `Asm.loc_external_result` -/
def locExternalResult (sg : Signature) : RPair Preg := RPair.map pregOf (locResult sg)

/-- `Asm.state` -/
inductive State where
  | State (rs : Regset) (m : Mem)

section RELSEM
variable (sym : HalfSplit) (ge : CGenv)

/-- `Asm.step` -/
inductive Step : State → Trace → State → Prop where
  | exec_step_internal (b ofs f i rs m rs' m') :
      rs .PC = .Vptr b ofs →
      Genv.findFunctPtr ge b = some (.Internal f) →
      findInstr (Integers.Ptrofs.unsigned ofs) f.fn_code = some i →
      execInstr sym ge f i rs m = .Next rs' m' →
      Step (.State rs m) E0 (.State rs' m')
  | exec_step_builtin (b ofs f ef args res) (rs : Regset) (m vargs t vres rs' m') :
      rs .PC = .Vptr b ofs →
      Genv.findFunctPtr ge b = some (.Internal f) →
      findInstr (Integers.Ptrofs.unsigned ofs) f.fn_code = some (.Pbuiltin ef args res) →
      EvalBuiltinArgs ge.toSenv rs (rs (.IR SP)) m args vargs →
      externalCall ef ge.toSenv vargs m t vres m' →
      rs' = nextinstr (setRes res vres
        (undefRegs ((destroyedByBuiltin ef).map pregOf)
          ((rs.set (.IR .X1) .Vundef).set (.IR .X31) .Vundef))) →
      Step (.State rs m) t (.State rs' m')
  | exec_step_external (b ef args res rs m t rs' m') :
      rs .PC = .Vptr b Integers.Ptrofs.zero →
      Genv.findFunctPtr ge b = some (.External ef) →
      externalCall ef ge.toSenv args m t res m' →
      ExtcallArguments rs m ef.sig args →
      rs' = (setPair (locExternalResult ef.sig) res (undefCallerSaveRegs rs)).set
        .PC (rs (.IR RA)) →
      Step (.State rs m) t (.State rs' m')

end RELSEM

/-- `Asm.initial_state` -/
inductive InitialState (p : Program) : State → Prop where
  | intro (m0) :
      p.initMem = some m0 →
      InitialState p (.State
        ((((Regset.init .Vundef).set .PC
          (Genv.symbolAddress p.globalenv p.prog_main Integers.Ptrofs.zero)).set
          (.IR SP) Val.Vnullptr).set (.IR RA) Val.Vnullptr) m0)

/-- `Asm.final_state`: the result is in `X10` (`a0`). -/
inductive FinalState : State → Integers.Int → Prop where
  | intro (rs m r) :
      rs .PC = Val.Vnullptr →
      rs (.IR .X10) = .Vint r →
      FinalState (.State rs m) r

/-- `Asm.semantics` -/
def semantics (sym : HalfSplit) (p : Program) : Semantics where
  state := State
  step := Step sym p.globalenv
  initial_state := InitialState p
  final_state := FinalState
  symbolenv := Genv.toSenv p.globalenv

theorem extcallArg_determ {rs m l v1 v2} (h1 : ExtcallArg rs m l v1)
    (h2 : ExtcallArg rs m l v2) : v1 = v2 := by
  cases h1 with
  | reg => cases h2; rfl
  | stack _ _ _ _ he h => cases h2 with
    | stack _ _ _ _ he' h' => subst he he'; rw [h] at h'; cases h'; rfl

theorem extcallArgPair_determ {rs m p v1 v2} (h1 : ExtcallArgPair rs m p v1)
    (h2 : ExtcallArgPair rs m p v2) : v1 = v2 := by
  cases h1 with
  | one _ _ h => cases h2 with
    | one _ _ h' => exact extcallArg_determ h h'
  | twolong _ _ _ _ ha hb => cases h2 with
    | twolong _ _ _ _ ha' hb' => rw [extcallArg_determ ha ha', extcallArg_determ hb hb']

/-- `Asm.extcall_arguments_determ` -/
theorem extcallArguments_determ {rs m sg args1 args2}
    (h1 : ExtcallArguments rs m sg args1) (h2 : ExtcallArguments rs m sg args2) :
    args1 = args2 := by
  unfold ExtcallArguments at h1 h2
  generalize locArguments sg = l at h1 h2
  induction h1 generalizing args2 with
  | nil => cases h2; rfl
  | cons ha _ ih => cases h2 with
    | cons hb hl => rw [extcallArgPair_determ ha hb, ih hl]

/-- `Asm.data_preg` -/
def dataPreg (r : Preg) : Bool :=
  match r with
  | .IR .X1 => false
  | .IR .X31 => false
  | .IR _ => true
  | .FR _ => true
  | .PC => false

end Asm
end RiscV
end CC
