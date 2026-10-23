/-
  Abstract syntax and semantics for AArch64 assembly language — port of
  `aarch64/Asm.v`.

  Ported: registers (`ireg`, `ireg0`, `iregsp`, `freg`, `crbit`, `preg`),
  `isize`, `fsize`, `testcond`, `addressing`, `shift_op`, `extend_op`, the
  instruction set, `function`, `fundef`, `program`, register sets and
  their operations (`ir0w`, `ir0x`, `undef_regs`, `undef_flags`,
  `set_pair`, `set_res`), `find_instr`, `is_label`, `label_pos`, `outcome`,
  `nextinstr`, `goto_label`, `eval_testcond`, `eval_testzero`,
  `eval_testbit`, `eval_addressing`, `exec_load`, `exec_store`,
  `compare_int`, `compare_long`, `compare_float`, `compare_single`,
  `insert_in_int`, `insert_in_long`, `eval_shift_op_int`,
  `eval_shift_op_long`, `eval_extend`, `float32_of_bits`,
  `float64_of_bits`, `exec_instr`, `preg_of`, `undef_caller_save_regs`,
  `extcall_arg`, `extcall_arg_pair`, `extcall_arguments`,
  `loc_external_result`, `state`, `step`, `initial_state`, `final_state`,
  `semantics`, `extcall_arguments_determ`, `data_preg`; also
  `Zbits.Zinsert`.

  Differences from Rocq:
  * The parameters `symbol_low`, `symbol_high` and the axiom
    `symbol_high_low` (how the linker splits `symbol + offset` into an ADRP
    part and a low part) are bundled in a structure `SymbolSplit`, an
    explicit argument of the semantics.  `Archi.abi` (used by
    `loc_arguments`) is an explicit argument `abi`.
  * The coercions `ireg >-> ireg0`, `ireg >-> iregsp`, `ireg >-> preg`, …
    are `Coe` instances; `Pregmap.t val` is the function type `Preg → Val`.
  * `semantics_determinate` is in `aarch64/AsmDeterm.lean`.
-/
import CCLib.backend.Mach

namespace CC

/-- `Zbits.Zinsert` -/
def Zinsert (x y : Z) (to len : Z) : Z :=
  -- `lor (land (shiftl y to) mask) (ldiff x mask)` with
  -- `mask = shiftl (2^len - 1) to`, computed arithmetically (the two
  -- operands of `lor` have disjoint bits).
  let p := (2 : Z) ^ to.toNat
  let q := (2 : Z) ^ len.toNat
  Int.emod y q * p + (x - Int.emod (Int.fdiv x p) q * p)

namespace Asm

open Op Smallstep Conventions1

/-! ## Abstract syntax -/

/-- `Asm.ireg` -/
inductive Ireg where
  | X0 | X1 | X2 | X3 | X4 | X5 | X6 | X7
  | X8 | X9 | X10 | X11 | X12 | X13 | X14 | X15
  | X16 | X17 | X18 | X19 | X20 | X21 | X22 | X23
  | X24 | X25 | X26 | X27 | X28 | X29 | X30
  deriving DecidableEq, Repr

/-- `Asm.ireg0` -/
inductive Ireg0 where
  | RR0 (r : Ireg)
  | XZR
  deriving DecidableEq, Repr

/-- `Asm.iregsp` -/
inductive Iregsp where
  | RR1 (r : Ireg)
  | XSP
  deriving DecidableEq, Repr

instance : Coe Ireg Ireg0 := ⟨.RR0⟩
instance : Coe Ireg Iregsp := ⟨.RR1⟩

/-- `Asm.freg` -/
inductive Freg where
  | D0 | D1 | D2 | D3 | D4 | D5 | D6 | D7
  | D8 | D9 | D10 | D11 | D12 | D13 | D14 | D15
  | D16 | D17 | D18 | D19 | D20 | D21 | D22 | D23
  | D24 | D25 | D26 | D27 | D28 | D29 | D30 | D31
  deriving DecidableEq, Repr

/-- `Asm.crbit` -/
inductive Crbit where
  | CN | CZ | CC | CV
  deriving DecidableEq, Repr

/-- `Asm.preg` -/
inductive Preg where
  | IR (r : Ireg)
  | FR (r : Freg)
  | CR (r : Crbit)
  | SP
  | PC
  deriving DecidableEq, Repr

instance : Coe Ireg Preg := ⟨.IR⟩
instance : Coe Freg Preg := ⟨.FR⟩
instance : Coe Crbit Preg := ⟨.CR⟩

/-- `Asm.preg_of_iregsp` -/
def pregOfIregsp (r : Iregsp) : Preg :=
  match r with
  | .RR1 r => .IR r
  | .XSP => .SP

instance : Coe Iregsp Preg := ⟨pregOfIregsp⟩

/-- The return address register `RA`. -/
abbrev RA : Ireg := .X30

/-- `Asm.label` -/
abbrev Label := Positive

/-- `Asm.isize` -/
inductive Isize where
  | W | X
  deriving DecidableEq, Repr

/-- `Asm.fsize` -/
inductive Fsize where
  | S | D
  deriving DecidableEq, Repr

/-- `Asm.testcond` -/
inductive Testcond where
  | TCeq | TCne | TChs | TClo | TCmi | TCpl | TChi | TCls | TCge | TClt | TCgt | TCle
  deriving DecidableEq, Repr

/-- `Asm.addressing` -/
inductive Addressing where
  | ADimm (base : Iregsp) (n : Integers.Int64)
  | ADreg (base : Iregsp) (r : Ireg)
  | ADlsl (base : Iregsp) (r : Ireg) (n : Integers.Int)
  | ADsxt (base : Iregsp) (r : Ireg) (n : Integers.Int)
  | ADuxt (base : Iregsp) (r : Ireg) (n : Integers.Int)
  | ADadr (base : Iregsp) (id : Ident) (ofs : Integers.Ptrofs)
  | ADpostincr (base : Iregsp) (n : Integers.Int64)
  | ADpreincr (base : Iregsp) (n : Integers.Int64)

/-- `Asm.shift_op` -/
inductive ShiftOp where
  | SOnone
  | SOlsl (n : Integers.Int)
  | SOlsr (n : Integers.Int)
  | SOasr (n : Integers.Int)
  | SOror (n : Integers.Int)

/-- `Asm.extend_op` -/
inductive ExtendOp where
  | EOsxtb (n : Integers.Int)
  | EOsxth (n : Integers.Int)
  | EOsxtw (n : Integers.Int)
  | EOuxtb (n : Integers.Int)
  | EOuxth (n : Integers.Int)
  | EOuxtw (n : Integers.Int)
  | EOuxtx (n : Integers.Int)

/-- `Asm.instruction` -/
inductive Instruction where
  -- Branches
  | Pb (lbl : Label)
  | Pbc (c : Testcond) (lbl : Label)
  | Pbl (id : Ident) (sg : Signature)
  | Pbs (id : Ident) (sg : Signature)
  | Pblr (r : Ireg) (sg : Signature)
  | Pbr (r : Ireg) (sg : Signature)
  | Pret (r : Ireg)
  | Pcbnz (sz : Isize) (r : Ireg) (lbl : Label)
  | Pcbz (sz : Isize) (r : Ireg) (lbl : Label)
  | Ptbnz (sz : Isize) (r : Ireg) (n : Integers.Int) (lbl : Label)
  | Ptbz (sz : Isize) (r : Ireg) (n : Integers.Int) (lbl : Label)
  -- Memory loads and stores
  | Pldrw (rd : Ireg) (a : Addressing)
  | Pldrw_a (rd : Ireg) (a : Addressing)
  | Pldrx (rd : Ireg) (a : Addressing)
  | Pldrx_a (rd : Ireg) (a : Addressing)
  | Pldrb (sz : Isize) (rd : Ireg) (a : Addressing)
  | Pldrsb (sz : Isize) (rd : Ireg) (a : Addressing)
  | Pldrh (sz : Isize) (rd : Ireg) (a : Addressing)
  | Pldrsh (sz : Isize) (rd : Ireg) (a : Addressing)
  | Pldrzw (rd : Ireg) (a : Addressing)
  | Pldrsw (rd : Ireg) (a : Addressing)
  | Pldp (rd1 rd2 : Ireg) (a : Addressing)
  | Pstrw (rs : Ireg) (a : Addressing)
  | Pstrw_a (rs : Ireg) (a : Addressing)
  | Pstrx (rs : Ireg) (a : Addressing)
  | Pstrx_a (rs : Ireg) (a : Addressing)
  | Pstrb (rs : Ireg) (a : Addressing)
  | Pstrh (rs : Ireg) (a : Addressing)
  | Pstp (rs1 rs2 : Ireg) (a : Addressing)
  -- Integer arithmetic, immediate
  | Paddimm (sz : Isize) (rd : Iregsp) (r1 : Iregsp) (n : Z)
  | Psubimm (sz : Isize) (rd : Iregsp) (r1 : Iregsp) (n : Z)
  | Pcmpimm (sz : Isize) (r1 : Ireg) (n : Z)
  | Pcmnimm (sz : Isize) (r1 : Ireg) (n : Z)
  -- Move integer register
  | Pmov (rd : Iregsp) (r1 : Iregsp)
  -- Logical, immediate
  | Pandimm (sz : Isize) (rd : Ireg) (r1 : Ireg0) (n : Z)
  | Peorimm (sz : Isize) (rd : Ireg) (r1 : Ireg0) (n : Z)
  | Porrimm (sz : Isize) (rd : Ireg) (r1 : Ireg0) (n : Z)
  | Ptstimm (sz : Isize) (r1 : Ireg) (n : Z)
  -- Move wide immediate
  | Pmovz (sz : Isize) (rd : Ireg) (n : Z) (pos : Z)
  | Pmovn (sz : Isize) (rd : Ireg) (n : Z) (pos : Z)
  | Pmovk (sz : Isize) (rd : Ireg) (n : Z) (pos : Z)
  -- PC-relative addressing
  | Padrp (rd : Ireg) (id : Ident) (ofs : Integers.Ptrofs)
  | Paddadr (rd : Ireg) (r1 : Ireg) (id : Ident) (ofs : Integers.Ptrofs)
  -- Bit-field operations
  | Psbfiz (sz : Isize) (rd : Ireg) (r1 : Ireg) (r : Integers.Int) (s : Z)
  | Psbfx (sz : Isize) (rd : Ireg) (r1 : Ireg) (r : Integers.Int) (s : Z)
  | Pubfiz (sz : Isize) (rd : Ireg) (r1 : Ireg) (r : Integers.Int) (s : Z)
  | Pubfx (sz : Isize) (rd : Ireg) (r1 : Ireg) (r : Integers.Int) (s : Z)
  -- Integer arithmetic, shifted register
  | Padd (sz : Isize) (rd : Ireg) (r1 : Ireg0) (r2 : Ireg) (s : ShiftOp)
  | Psub (sz : Isize) (rd : Ireg) (r1 : Ireg0) (r2 : Ireg) (s : ShiftOp)
  | Pcmp (sz : Isize) (r1 : Ireg0) (r2 : Ireg) (s : ShiftOp)
  | Pcmn (sz : Isize) (r1 : Ireg0) (r2 : Ireg) (s : ShiftOp)
  -- Integer arithmetic, extending register
  | Paddext (rd : Iregsp) (r1 : Iregsp) (r2 : Ireg) (x : ExtendOp)
  | Psubext (rd : Iregsp) (r1 : Iregsp) (r2 : Ireg) (x : ExtendOp)
  | Pcmpext (r1 : Ireg) (r2 : Ireg) (x : ExtendOp)
  | Pcmnext (r1 : Ireg) (r2 : Ireg) (x : ExtendOp)
  -- Logical, shifted register
  | Pand (sz : Isize) (rd : Ireg) (r1 : Ireg0) (r2 : Ireg) (s : ShiftOp)
  | Pbic (sz : Isize) (rd : Ireg) (r1 : Ireg0) (r2 : Ireg) (s : ShiftOp)
  | Peon (sz : Isize) (rd : Ireg) (r1 : Ireg0) (r2 : Ireg) (s : ShiftOp)
  | Peor (sz : Isize) (rd : Ireg) (r1 : Ireg0) (r2 : Ireg) (s : ShiftOp)
  | Porr (sz : Isize) (rd : Ireg) (r1 : Ireg0) (r2 : Ireg) (s : ShiftOp)
  | Porn (sz : Isize) (rd : Ireg) (r1 : Ireg0) (r2 : Ireg) (s : ShiftOp)
  | Ptst (sz : Isize) (r1 : Ireg0) (r2 : Ireg) (s : ShiftOp)
  -- Variable shifts
  | Pasrv (sz : Isize) (rd : Ireg) (r1 r2 : Ireg)
  | Plslv (sz : Isize) (rd : Ireg) (r1 r2 : Ireg)
  | Plsrv (sz : Isize) (rd : Ireg) (r1 r2 : Ireg)
  | Prorv (sz : Isize) (rd : Ireg) (r1 r2 : Ireg)
  -- Bit operations
  | Pcls (sz : Isize) (rd r1 : Ireg)
  | Pclz (sz : Isize) (rd r1 : Ireg)
  | Prev (sz : Isize) (rd r1 : Ireg)
  | Prev16 (sz : Isize) (rd r1 : Ireg)
  | Prbit (sz : Isize) (rd r1 : Ireg)
  -- Conditional data processing
  | Pcsel (rd : Ireg) (r1 r2 : Ireg) (c : Testcond)
  | Pcset (rd : Ireg) (c : Testcond)
  -- Integer multiply/divide
  | Pmadd (sz : Isize) (rd : Ireg) (r1 r2 : Ireg) (r3 : Ireg0)
  | Pmsub (sz : Isize) (rd : Ireg) (r1 r2 : Ireg) (r3 : Ireg0)
  | Psmulh (rd : Ireg) (r1 r2 : Ireg)
  | Pumulh (rd : Ireg) (r1 r2 : Ireg)
  | Psdiv (sz : Isize) (rd : Ireg) (r1 r2 : Ireg)
  | Pudiv (sz : Isize) (rd : Ireg) (r1 r2 : Ireg)
  -- Floating-point loads and stores
  | Pldrs (rd : Freg) (a : Addressing)
  | Pldrd (rd : Freg) (a : Addressing)
  | Pldrd_a (rd : Freg) (a : Addressing)
  | Pstrs (rs : Freg) (a : Addressing)
  | Pstrd (rs : Freg) (a : Addressing)
  | Pstrd_a (rs : Freg) (a : Addressing)
  -- Floating-point move
  | Pfmov (rd r1 : Freg)
  | Pfmovimms (rd : Freg) (f : Floats.Float32)
  | Pfmovimmd (rd : Freg) (f : Floats.Float)
  | Pfmovi (fsz : Fsize) (rd : Freg) (r1 : Ireg0)
  -- Floating-point conversions
  | Pfcvtds (rd r1 : Freg)
  | Pfcvtsd (rd r1 : Freg)
  | Pfcvtzs (isz : Isize) (fsz : Fsize) (rd : Ireg) (r1 : Freg)
  | Pfcvtzu (isz : Isize) (fsz : Fsize) (rd : Ireg) (r1 : Freg)
  | Pscvtf (fsz : Fsize) (isz : Isize) (rd : Freg) (r1 : Ireg)
  | Pucvtf (fsz : Fsize) (isz : Isize) (rd : Freg) (r1 : Ireg)
  -- Floating-point arithmetic
  | Pfabs (sz : Fsize) (rd r1 : Freg)
  | Pfneg (sz : Fsize) (rd r1 : Freg)
  | Pfsqrt (sz : Fsize) (rd r1 : Freg)
  | Pfadd (sz : Fsize) (rd r1 r2 : Freg)
  | Pfdiv (sz : Fsize) (rd r1 r2 : Freg)
  | Pfmul (sz : Fsize) (rd r1 r2 : Freg)
  | Pfnmul (sz : Fsize) (rd r1 r2 : Freg)
  | Pfsub (sz : Fsize) (rd r1 r2 : Freg)
  | Pfmadd (sz : Fsize) (rd r1 r2 r3 : Freg)
  | Pfmsub (sz : Fsize) (rd r1 r2 r3 : Freg)
  | Pfnmadd (sz : Fsize) (rd r1 r2 r3 : Freg)
  | Pfnmsub (sz : Fsize) (rd r1 r2 r3 : Freg)
  | Pfmax (sz : Fsize) (rd r1 r2 : Freg)
  | Pfmin (sz : Fsize) (rd r1 r2 : Freg)
  -- Floating-point comparison
  | Pfcmp (sz : Fsize) (r1 r2 : Freg)
  | Pfcmp0 (sz : Fsize) (r1 : Freg)
  -- Floating-point conditional select
  | Pfsel (rd r1 r2 : Freg) (cond : Testcond)
  -- Pseudo-instructions
  | Pallocframe (sz : Z) (linkofs : Integers.Ptrofs) (retaddrofs : Integers.Ptrofs)
  | Pfreeframe (sz : Z) (linkofs : Integers.Ptrofs)
  | Plabel (lbl : Label)
  | Ploadsymbol (rd : Ireg) (id : Ident)
  | Pcvtsw2x (rd : Ireg) (r1 : Ireg)
  | Pcvtuw2x (rd : Ireg) (r1 : Ireg)
  | Pcvtx2w (rd : Ireg)
  | Pbtbl (r1 : Ireg) (tbl : List Label)
  | Pbuiltin (ef : ExtFun) (args : List (BuiltinArg Preg)) (res : BuiltinRes Preg)
  | Pnop
  | Pcfi_adjust (ofs : Integers.Int)
  | Pcfi_rel_offset (ofs : Integers.Int)

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

/-- `Asm.ir0w` -/
def ir0w (rs : Regset) (r : Ireg0) : Val :=
  match r with
  | .RR0 r => rs (.IR r)
  | .XZR => .Vint Integers.Int.zero

/-- `Asm.ir0x` -/
def ir0x (rs : Regset) (r : Ireg0) : Val :=
  match r with
  | .RR0 r => rs (.IR r)
  | .XZR => .Vlong Integers.Int64.zero

/-- `Asm.undef_regs` -/
def undefRegs : List Preg → Regset → Regset
  | [], rs => rs
  | r :: l', rs => undefRegs l' (rs.set r .Vundef)

/-- `Asm.undef_flags` -/
def undefFlags (rs : Regset) : Regset := fun r =>
  match r with
  | .CR _ => .Vundef
  | _ => rs r

/-- `Asm.set_pair` -/
def setPair (p : RPair Preg) (v : Val) (rs : Regset) : Regset :=
  match p with
  | .One r => rs.set r v
  | .Twolong rhi rlo => (rs.set rhi (Val.hiword v)).set rlo (Val.loword v)

/-- `Asm.set_res` -/
def setRes : BuiltinRes Preg → Val → Regset → Regset
  | .BR r, v, rs => rs.set r v
  | .BR_none, _, rs => rs
  | .BR_splitlong hi lo, v, rs => setRes lo (Val.loword v) (setRes hi (Val.hiword v) rs)

/-- The parameters `Asm.symbol_low`, `Asm.symbol_high` and the axiom
    `Asm.symbol_high_low`: how the linker splits the address of
    `symbol + offset` into a high part (argument of ADRP) and a low part
    (usable as an offset in an addressing mode). -/
structure SymbolSplit where
  symbol_low : CGenv → Ident → Integers.Ptrofs → Val
  symbol_high : CGenv → Ident → Integers.Ptrofs → Val
  symbol_high_low : ∀ ge id ofs,
    Val.addl (symbol_high ge id ofs) (symbol_low ge id ofs) = Genv.symbolAddress ge id ofs

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

/-- `Asm.eval_testcond` -/
def evalTestcond (c : Testcond) (rs : Regset) : Option Bool :=
  match c with
  | .TCeq => match rs (.CR .CZ) with
    | .Vint n => some (Integers.Int.eq n Integers.Int.one)
    | _ => none
  | .TCne => match rs (.CR .CZ) with
    | .Vint n => some (Integers.Int.eq n Integers.Int.zero)
    | _ => none
  | .TClo => match rs (.CR .CC) with
    | .Vint n => some (Integers.Int.eq n Integers.Int.zero)
    | _ => none
  | .TCls => match rs (.CR .CC), rs (.CR .CZ) with
    | .Vint c, .Vint z => some (Integers.Int.eq c Integers.Int.zero || Integers.Int.eq z Integers.Int.one)
    | _, _ => none
  | .TChs => match rs (.CR .CC) with
    | .Vint n => some (Integers.Int.eq n Integers.Int.one)
    | _ => none
  | .TChi => match rs (.CR .CC), rs (.CR .CZ) with
    | .Vint c, .Vint z => some (Integers.Int.eq c Integers.Int.one && Integers.Int.eq z Integers.Int.zero)
    | _, _ => none
  | .TClt => match rs (.CR .CV), rs (.CR .CN) with
    | .Vint o, .Vint s => some (Integers.Int.eq (Integers.Int.xor o s) Integers.Int.one)
    | _, _ => none
  | .TCle => match rs (.CR .CV), rs (.CR .CN), rs (.CR .CZ) with
    | .Vint o, .Vint s, .Vint z => some (Integers.Int.eq (Integers.Int.xor o s) Integers.Int.one || Integers.Int.eq z Integers.Int.one)
    | _, _, _ => none
  | .TCge => match rs (.CR .CV), rs (.CR .CN) with
    | .Vint o, .Vint s => some (Integers.Int.eq (Integers.Int.xor o s) Integers.Int.zero)
    | _, _ => none
  | .TCgt => match rs (.CR .CV), rs (.CR .CN), rs (.CR .CZ) with
    | .Vint o, .Vint s, .Vint z => some (Integers.Int.eq (Integers.Int.xor o s) Integers.Int.zero && Integers.Int.eq z Integers.Int.zero)
    | _, _, _ => none
  | .TCpl => match rs (.CR .CN) with
    | .Vint n => some (Integers.Int.eq n Integers.Int.zero)
    | _ => none
  | .TCmi => match rs (.CR .CN) with
    | .Vint n => some (Integers.Int.eq n Integers.Int.one)
    | _ => none

/-- `Asm.eval_testzero` -/
def evalTestzero (sz : Isize) (v : Val) (m : Mem) : Option Bool :=
  match sz with
  | .W => Val.cmpu_bool (Mem.validPointer m) .Ceq v (.Vint Integers.Int.zero)
  | .X => Val.cmplu_bool (Mem.validPointer m) .Ceq v (.Vlong Integers.Int64.zero)

/-- `Asm.eval_testbit` -/
def evalTestbit (sz : Isize) (v : Val) (n : Integers.Int) : Option Bool :=
  match sz with
  | .W => Val.cmp_bool .Cne (Val.and v (.Vint (Integers.Int.shl Integers.Int.one n)))
      (.Vint Integers.Int.zero)
  | .X => Val.cmpl_bool .Cne (Val.andl v (.Vlong (Integers.Int64.shl' Integers.Int64.one n)))
      (.Vlong Integers.Int64.zero)

/-- `Asm.compare_int` -/
def compareInt (rs : Regset) (v1 v2 : Val) (m : Mem) : Regset :=
  (((rs.set (.CR .CN) (Val.negative (Val.sub v1 v2))).set
    (.CR .CZ) (Val.cmpu (Mem.validPointer m) .Ceq v1 v2)).set
    (.CR .CC) (Val.cmpu (Mem.validPointer m) .Cge v1 v2)).set
    (.CR .CV) (Val.sub_overflow v1 v2)

/-- `Asm.compare_long` -/
def compareLong (rs : Regset) (v1 v2 : Val) (m : Mem) : Regset :=
  (((rs.set (.CR .CN) (Val.negativel (Val.subl v1 v2))).set
    (.CR .CZ) (Val.maketotal (Val.cmplu (Mem.validPointer m) .Ceq v1 v2))).set
    (.CR .CC) (Val.maketotal (Val.cmplu (Mem.validPointer m) .Cge v1 v2))).set
    (.CR .CV) (Val.subl_overflow v1 v2)

/-- Setting the four flags (helper for `compare_float` / `compare_single`). -/
def setFlags (rs : Regset) (n z c v : Val) : Regset :=
  (((rs.set (.CR .CN) n).set (.CR .CZ) z).set (.CR .CC) c).set (.CR .CV) v

/-- `Asm.compare_float` -/
def compareFloat (rs : Regset) (v1 v2 : Val) : Regset :=
  match v1, v2 with
  | .Vfloat f1, .Vfloat f2 =>
      setFlags rs (Val.ofBool (Floats.Float.cmp .Clt f1 f2)) (Val.ofBool (Floats.Float.cmp .Ceq f1 f2))
        (Val.ofBool (!(Floats.Float.cmp .Clt f1 f2))) (Val.ofBool (!(Floats.Float.ordered f1 f2)))
  | _, _ => setFlags rs .Vundef .Vundef .Vundef .Vundef

/-- `Asm.compare_single` -/
def compareSingle (rs : Regset) (v1 v2 : Val) : Regset :=
  match v1, v2 with
  | .Vsingle f1, .Vsingle f2 =>
      setFlags rs (Val.ofBool (Floats.Float32.cmp .Clt f1 f2))
        (Val.ofBool (Floats.Float32.cmp .Ceq f1 f2))
        (Val.ofBool (!(Floats.Float32.cmp .Clt f1 f2)))
        (Val.ofBool (!(Floats.Float32.ordered f1 f2)))
  | _, _ => setFlags rs .Vundef .Vundef .Vundef .Vundef

/-- `Asm.insert_in_int` -/
def insertInInt (x : Val) (y pos len : Z) : Val :=
  match x with
  | .Vint n => .Vint (Integers.Int.repr (Zinsert (Integers.Int.unsigned n) y pos len))
  | _ => .Vundef

/-- `Asm.insert_in_long` -/
def insertInLong (x : Val) (y pos len : Z) : Val :=
  match x with
  | .Vlong n => .Vlong (Integers.Int64.repr (Zinsert (Integers.Int64.unsigned n) y pos len))
  | _ => .Vundef

/-- `Asm.eval_shift_op_int` -/
def evalShiftOpInt (v : Val) (s : ShiftOp) : Val :=
  match s with
  | .SOnone => v
  | .SOlsl n => Val.shl v (.Vint n)
  | .SOlsr n => Val.shru v (.Vint n)
  | .SOasr n => Val.shr v (.Vint n)
  | .SOror n => Val.ror v (.Vint n)

/-- `Asm.eval_shift_op_long` -/
def evalShiftOpLong (v : Val) (s : ShiftOp) : Val :=
  match s with
  | .SOnone => v
  | .SOlsl n => Val.shll v (.Vint n)
  | .SOlsr n => Val.shrlu v (.Vint n)
  | .SOasr n => Val.shrl v (.Vint n)
  | .SOror n => Val.rorl v (.Vint n)

/-- `Asm.eval_extend` -/
def evalExtend (v : Val) (x : ExtendOp) : Val :=
  match x with
  | .EOsxtb n => Val.shll (Val.longofint (Val.signExt 8 v)) (.Vint n)
  | .EOsxth n => Val.shll (Val.longofint (Val.signExt 16 v)) (.Vint n)
  | .EOsxtw n => Val.shll (Val.longofint v) (.Vint n)
  | .EOuxtb n => Val.shll (Val.longofintu (Val.zeroExt 8 v)) (.Vint n)
  | .EOuxth n => Val.shll (Val.longofintu (Val.zeroExt 16 v)) (.Vint n)
  | .EOuxtw n => Val.shll (Val.longofintu v) (.Vint n)
  | .EOuxtx n => Val.shll v (.Vint n)

/-- `Asm.float32_of_bits` -/
def float32OfBits (v : Val) : Val :=
  match v with
  | .Vint n => .Vsingle (Floats.Float32.ofBits n)
  | _ => .Vundef

/-- `Asm.float64_of_bits` -/
def float64OfBits (v : Val) : Val :=
  match v with
  | .Vlong n => .Vfloat (Floats.Float.ofBits n)
  | _ => .Vundef

section RELSEM
variable (sym : SymbolSplit) (ge : CGenv)

/-- `Asm.eval_addressing` -/
def evalAddressing (a : Addressing) (rs : Regset) : Val :=
  match a with
  | .ADimm base n => Val.addl (rs base) (.Vlong n)
  | .ADreg base r => Val.addl (rs base) (rs r)
  | .ADlsl base r n => Val.addl (rs base) (Val.shll (rs r) (.Vint n))
  | .ADsxt base r n => Val.addl (rs base) (Val.shll (Val.longofint (rs r)) (.Vint n))
  | .ADuxt base r n => Val.addl (rs base) (Val.shll (Val.longofintu (rs r)) (.Vint n))
  | .ADadr base id ofs => Val.addl (rs base) (sym.symbol_low ge id ofs)
  | .ADpostincr _ _ => .Vundef
  | .ADpreincr _ _ => .Vundef

/-- `Asm.exec_load` -/
def execLoad (chunk : Chunk) (transf : Val → Val) (a : Addressing) (r : Preg) (rs : Regset)
    (m : Mem) : Outcome :=
  match Mem.loadv chunk m (evalAddressing sym ge a rs) with
  | none => .Stuck
  | some v => .Next (nextinstr (rs.set r (transf v))) m

/-- `Asm.exec_store` -/
def execStore (chunk : Chunk) (a : Addressing) (v : Val) (rs : Regset) (m : Mem) : Outcome :=
  match Mem.storev chunk m (evalAddressing sym ge a rs) v with
  | none => .Stuck
  | some m' => .Next (nextinstr rs) m'

/-- `Next (nextinstr (rs # rd <- v)) m` -/
abbrev nextSet (rs : Regset) (rd : Preg) (v : Val) (m : Mem) : Outcome :=
  .Next (nextinstr (rs.set rd v)) m

/-- Conditional selection of `Pcsel` / `Pfsel`. -/
def selectCond (c : Testcond) (rs : Regset) (v1 v2 : Val) : Val :=
  match evalTestcond c rs with
  | some true => v1
  | some false => v2
  | none => .Vundef

/-- `Asm.exec_instr` -/
def execInstr (f : Function) (i : Instruction) (rs : Regset) (m : Mem) : Outcome :=
  let load := execLoad sym ge
  let store := execStore sym ge
  match i with
  -- Branches
  | .Pb lbl => gotoLabel f lbl rs m
  | .Pbc cond lbl =>
      match evalTestcond cond rs with
      | some true => gotoLabel f lbl rs m
      | some false => .Next (nextinstr rs) m
      | none => .Stuck
  | .Pbl id _ =>
      .Next ((rs.set (.IR RA) (Val.offsetPtr (rs .PC) Integers.Ptrofs.one)).set .PC
        (Genv.symbolAddress ge id Integers.Ptrofs.zero)) m
  | .Pbs id _ => .Next (rs.set .PC (Genv.symbolAddress ge id Integers.Ptrofs.zero)) m
  | .Pblr r _ => .Next ((rs.set (.IR RA) (Val.offsetPtr (rs .PC) Integers.Ptrofs.one)).set .PC (rs r)) m
  | .Pbr r _ => .Next (rs.set .PC (rs r)) m
  | .Pret r => .Next (rs.set .PC (rs r)) m
  | .Pcbnz sz r lbl =>
      match evalTestzero sz (rs r) m with
      | some true => .Next (nextinstr rs) m
      | some false => gotoLabel f lbl rs m
      | none => .Stuck
  | .Pcbz sz r lbl =>
      match evalTestzero sz (rs r) m with
      | some true => gotoLabel f lbl rs m
      | some false => .Next (nextinstr rs) m
      | none => .Stuck
  | .Ptbnz sz r n lbl =>
      match evalTestbit sz (rs r) n with
      | some true => gotoLabel f lbl rs m
      | some false => .Next (nextinstr rs) m
      | none => .Stuck
  | .Ptbz sz r n lbl =>
      match evalTestbit sz (rs r) n with
      | some true => .Next (nextinstr rs) m
      | some false => gotoLabel f lbl rs m
      | none => .Stuck
  -- Memory loads and stores
  | .Pldrw rd a => load .Mint32 id a rd rs m
  | .Pldrw_a rd a => load .Many32 id a rd rs m
  | .Pldrx rd a => load .Mint64 id a rd rs m
  | .Pldrx_a rd a => load .Many64 id a rd rs m
  | .Pldrb .W rd a => load .Mint8unsigned id a rd rs m
  | .Pldrb .X rd a => load .Mint8unsigned Val.longofintu a rd rs m
  | .Pldrsb .W rd a => load .Mint8signed id a rd rs m
  | .Pldrsb .X rd a => load .Mint8signed Val.longofint a rd rs m
  | .Pldrh .W rd a => load .Mint16unsigned id a rd rs m
  | .Pldrh .X rd a => load .Mint16unsigned Val.longofintu a rd rs m
  | .Pldrsh .W rd a => load .Mint16signed id a rd rs m
  | .Pldrsh .X rd a => load .Mint16signed Val.longofint a rd rs m
  | .Pldrzw rd a => load .Mint32 Val.longofintu a rd rs m
  | .Pldrsw rd a => load .Mint32 Val.longofint a rd rs m
  | .Pstrw r a => store .Mint32 a (rs r) rs m
  | .Pstrw_a r a => store .Many32 a (rs r) rs m
  | .Pstrx r a => store .Mint64 a (rs r) rs m
  | .Pstrx_a r a => store .Many64 a (rs r) rs m
  | .Pstrb r a => store .Mint8unsigned a (rs r) rs m
  | .Pstrh r a => store .Mint16unsigned a (rs r) rs m
  -- Integer arithmetic, immediate
  | .Paddimm .W rd r1 n => nextSet rs rd (Val.add (rs r1) (.Vint (Integers.Int.repr n))) m
  | .Paddimm .X rd r1 n => nextSet rs rd (Val.addl (rs r1) (.Vlong (Integers.Int64.repr n))) m
  | .Psubimm .W rd r1 n => nextSet rs rd (Val.sub (rs r1) (.Vint (Integers.Int.repr n))) m
  | .Psubimm .X rd r1 n => nextSet rs rd (Val.subl (rs r1) (.Vlong (Integers.Int64.repr n))) m
  | .Pcmpimm .W r1 n => .Next (nextinstr (compareInt rs (rs r1) (.Vint (Integers.Int.repr n)) m)) m
  | .Pcmpimm .X r1 n => .Next (nextinstr (compareLong rs (rs r1) (.Vlong (Integers.Int64.repr n)) m)) m
  | .Pcmnimm .W r1 n =>
      .Next (nextinstr (compareInt rs (rs r1) (.Vint (Integers.Int.neg (Integers.Int.repr n))) m)) m
  | .Pcmnimm .X r1 n =>
      .Next (nextinstr (compareLong rs (rs r1) (.Vlong (Integers.Int64.neg (Integers.Int64.repr n))) m)) m
  -- Move integer register
  | .Pmov rd r1 => nextSet rs rd (rs r1) m
  -- Logical, immediate
  | .Pandimm .W rd r1 n => nextSet rs rd (Val.and (ir0w rs r1) (.Vint (Integers.Int.repr n))) m
  | .Pandimm .X rd r1 n => nextSet rs rd (Val.andl (ir0x rs r1) (.Vlong (Integers.Int64.repr n))) m
  | .Peorimm .W rd r1 n => nextSet rs rd (Val.xor (ir0w rs r1) (.Vint (Integers.Int.repr n))) m
  | .Peorimm .X rd r1 n => nextSet rs rd (Val.xorl (ir0x rs r1) (.Vlong (Integers.Int64.repr n))) m
  | .Porrimm .W rd r1 n => nextSet rs rd (Val.or (ir0w rs r1) (.Vint (Integers.Int.repr n))) m
  | .Porrimm .X rd r1 n => nextSet rs rd (Val.orl (ir0x rs r1) (.Vlong (Integers.Int64.repr n))) m
  | .Ptstimm .W r1 n =>
      .Next (nextinstr (compareInt rs (Val.and (rs r1) (.Vint (Integers.Int.repr n))) (.Vint Integers.Int.zero) m)) m
  | .Ptstimm .X r1 n =>
      .Next (nextinstr (compareLong rs (Val.andl (rs r1) (.Vlong (Integers.Int64.repr n)))
        (.Vlong Integers.Int64.zero) m)) m
  -- Move wide immediate
  | .Pmovz .W rd n pos => nextSet rs rd (.Vint (Integers.Int.repr (n <<< pos.toNat))) m
  | .Pmovz .X rd n pos => nextSet rs rd (.Vlong (Integers.Int64.repr (n <<< pos.toNat))) m
  | .Pmovn .W rd n pos => nextSet rs rd (.Vint (Integers.Int.repr (-(n <<< pos.toNat) - 1))) m
  | .Pmovn .X rd n pos => nextSet rs rd (.Vlong (Integers.Int64.repr (-(n <<< pos.toNat) - 1))) m
  | .Pmovk .W rd n pos => nextSet rs rd (insertInInt (rs rd) n pos 16) m
  | .Pmovk .X rd n pos => nextSet rs rd (insertInLong (rs rd) n pos 16) m
  -- PC-relative addressing
  | .Padrp rd id ofs => nextSet rs rd (sym.symbol_high ge id ofs) m
  | .Paddadr rd r1 id ofs => nextSet rs rd (Val.addl (rs r1) (sym.symbol_low ge id ofs)) m
  -- Bit-field operations
  | .Psbfiz .W rd r1 r s => nextSet rs rd (Val.shl (Val.signExt s.toNat (rs r1)) (.Vint r)) m
  | .Psbfiz .X rd r1 r s => nextSet rs rd (Val.shll (Val.sign_ext_l s.toNat (rs r1)) (.Vint r)) m
  | .Psbfx .W rd r1 r s => nextSet rs rd (Val.signExt s.toNat (Val.shr (rs r1) (.Vint r))) m
  | .Psbfx .X rd r1 r s => nextSet rs rd (Val.sign_ext_l s.toNat (Val.shrl (rs r1) (.Vint r))) m
  | .Pubfiz .W rd r1 r s => nextSet rs rd (Val.shl (Val.zeroExt s.toNat (rs r1)) (.Vint r)) m
  | .Pubfiz .X rd r1 r s => nextSet rs rd (Val.shll (Val.zero_ext_l s.toNat (rs r1)) (.Vint r)) m
  | .Pubfx .W rd r1 r s => nextSet rs rd (Val.zeroExt s.toNat (Val.shru (rs r1) (.Vint r))) m
  | .Pubfx .X rd r1 r s => nextSet rs rd (Val.zero_ext_l s.toNat (Val.shrlu (rs r1) (.Vint r))) m
  -- Integer arithmetic, shifted register
  | .Padd .W rd r1 r2 s => nextSet rs rd (Val.add (ir0w rs r1) (evalShiftOpInt (rs r2) s)) m
  | .Padd .X rd r1 r2 s => nextSet rs rd (Val.addl (ir0x rs r1) (evalShiftOpLong (rs r2) s)) m
  | .Psub .W rd r1 r2 s => nextSet rs rd (Val.sub (ir0w rs r1) (evalShiftOpInt (rs r2) s)) m
  | .Psub .X rd r1 r2 s => nextSet rs rd (Val.subl (ir0x rs r1) (evalShiftOpLong (rs r2) s)) m
  | .Pcmp .W r1 r2 s =>
      .Next (nextinstr (compareInt rs (ir0w rs r1) (evalShiftOpInt (rs r2) s) m)) m
  | .Pcmp .X r1 r2 s =>
      .Next (nextinstr (compareLong rs (ir0x rs r1) (evalShiftOpLong (rs r2) s) m)) m
  | .Pcmn .W r1 r2 s =>
      .Next (nextinstr (compareInt rs (ir0w rs r1) (Val.neg (evalShiftOpInt (rs r2) s)) m)) m
  | .Pcmn .X r1 r2 s =>
      .Next (nextinstr (compareLong rs (ir0x rs r1) (Val.negl (evalShiftOpLong (rs r2) s)) m)) m
  -- Integer arithmetic, extending register
  | .Paddext rd r1 r2 x => nextSet rs rd (Val.addl (rs r1) (evalExtend (rs r2) x)) m
  | .Psubext rd r1 r2 x => nextSet rs rd (Val.subl (rs r1) (evalExtend (rs r2) x)) m
  | .Pcmpext r1 r2 x => .Next (nextinstr (compareLong rs (rs r1) (evalExtend (rs r2) x) m)) m
  | .Pcmnext r1 r2 x =>
      .Next (nextinstr (compareLong rs (rs r1) (Val.negl (evalExtend (rs r2) x)) m)) m
  -- Logical, shifted register
  | .Pand .W rd r1 r2 s => nextSet rs rd (Val.and (ir0w rs r1) (evalShiftOpInt (rs r2) s)) m
  | .Pand .X rd r1 r2 s => nextSet rs rd (Val.andl (ir0x rs r1) (evalShiftOpLong (rs r2) s)) m
  | .Pbic .W rd r1 r2 s =>
      nextSet rs rd (Val.and (ir0w rs r1) (Val.notint (evalShiftOpInt (rs r2) s))) m
  | .Pbic .X rd r1 r2 s =>
      nextSet rs rd (Val.andl (ir0x rs r1) (Val.notl (evalShiftOpLong (rs r2) s))) m
  | .Peon .W rd r1 r2 s =>
      nextSet rs rd (Val.xor (ir0w rs r1) (Val.notint (evalShiftOpInt (rs r2) s))) m
  | .Peon .X rd r1 r2 s =>
      nextSet rs rd (Val.xorl (ir0x rs r1) (Val.notl (evalShiftOpLong (rs r2) s))) m
  | .Peor .W rd r1 r2 s => nextSet rs rd (Val.xor (ir0w rs r1) (evalShiftOpInt (rs r2) s)) m
  | .Peor .X rd r1 r2 s => nextSet rs rd (Val.xorl (ir0x rs r1) (evalShiftOpLong (rs r2) s)) m
  | .Porr .W rd r1 r2 s => nextSet rs rd (Val.or (ir0w rs r1) (evalShiftOpInt (rs r2) s)) m
  | .Porr .X rd r1 r2 s => nextSet rs rd (Val.orl (ir0x rs r1) (evalShiftOpLong (rs r2) s)) m
  | .Porn .W rd r1 r2 s =>
      nextSet rs rd (Val.or (ir0w rs r1) (Val.notint (evalShiftOpInt (rs r2) s))) m
  | .Porn .X rd r1 r2 s =>
      nextSet rs rd (Val.orl (ir0x rs r1) (Val.notl (evalShiftOpLong (rs r2) s))) m
  | .Ptst .W r1 r2 s =>
      .Next (nextinstr (compareInt rs (Val.and (ir0w rs r1) (evalShiftOpInt (rs r2) s))
        (.Vint Integers.Int.zero) m)) m
  | .Ptst .X r1 r2 s =>
      .Next (nextinstr (compareLong rs (Val.andl (ir0x rs r1) (evalShiftOpLong (rs r2) s))
        (.Vlong Integers.Int64.zero) m)) m
  -- Variable shifts
  | .Pasrv .W rd r1 r2 => nextSet rs rd (Val.shr (rs r1) (rs r2)) m
  | .Pasrv .X rd r1 r2 => nextSet rs rd (Val.shrl (rs r1) (rs r2)) m
  | .Plslv .W rd r1 r2 => nextSet rs rd (Val.shl (rs r1) (rs r2)) m
  | .Plslv .X rd r1 r2 => nextSet rs rd (Val.shll (rs r1) (rs r2)) m
  | .Plsrv .W rd r1 r2 => nextSet rs rd (Val.shru (rs r1) (rs r2)) m
  | .Plsrv .X rd r1 r2 => nextSet rs rd (Val.shrlu (rs r1) (rs r2)) m
  | .Prorv .W rd r1 r2 => nextSet rs rd (Val.ror (rs r1) (rs r2)) m
  | .Prorv .X rd r1 r2 => nextSet rs rd (Val.rorl (rs r1) (rs r2)) m
  -- Conditional data processing
  | .Pcsel rd r1 r2 cond => nextSet rs rd (selectCond cond rs (rs r1) (rs r2)) m
  | .Pcset rd cond => nextSet rs rd (selectCond cond rs (.Vint Integers.Int.one) (.Vint Integers.Int.zero)) m
  -- Integer multiply/divide
  | .Pmadd .W rd r1 r2 r3 => nextSet rs rd (Val.add (ir0w rs r3) (Val.mul (rs r1) (rs r2))) m
  | .Pmadd .X rd r1 r2 r3 => nextSet rs rd (Val.addl (ir0x rs r3) (Val.mull (rs r1) (rs r2))) m
  | .Pmsub .W rd r1 r2 r3 => nextSet rs rd (Val.sub (ir0w rs r3) (Val.mul (rs r1) (rs r2))) m
  | .Pmsub .X rd r1 r2 r3 => nextSet rs rd (Val.subl (ir0x rs r3) (Val.mull (rs r1) (rs r2))) m
  | .Psmulh rd r1 r2 => nextSet rs rd (Val.mullhs (rs r1) (rs r2)) m
  | .Pumulh rd r1 r2 => nextSet rs rd (Val.mullhu (rs r1) (rs r2)) m
  | .Psdiv .W rd r1 r2 => nextSet rs rd (Val.maketotal (Val.divs (rs r1) (rs r2))) m
  | .Psdiv .X rd r1 r2 => nextSet rs rd (Val.maketotal (Val.divls (rs r1) (rs r2))) m
  | .Pudiv .W rd r1 r2 => nextSet rs rd (Val.maketotal (Val.divu (rs r1) (rs r2))) m
  | .Pudiv .X rd r1 r2 => nextSet rs rd (Val.maketotal (Val.divlu (rs r1) (rs r2))) m
  -- Floating-point loads and stores
  | .Pldrs rd a => load .Mfloat32 id a rd rs m
  | .Pldrd rd a => load .Mfloat64 id a rd rs m
  | .Pldrd_a rd a => load .Many64 id a rd rs m
  | .Pstrs r a => store .Mfloat32 a (rs r) rs m
  | .Pstrd r a => store .Mfloat64 a (rs r) rs m
  | .Pstrd_a r a => store .Many64 a (rs r) rs m
  -- Floating-point move
  | .Pfmov rd r1 => nextSet rs rd (rs r1) m
  | .Pfmovimms rd f => .Next (nextinstr ((rs.set (.IR .X16) .Vundef).set rd (.Vsingle f))) m
  | .Pfmovimmd rd f => .Next (nextinstr ((rs.set (.IR .X16) .Vundef).set rd (.Vfloat f))) m
  | .Pfmovi .S rd r1 => nextSet rs rd (float32OfBits (ir0w rs r1)) m
  | .Pfmovi .D rd r1 => nextSet rs rd (float64OfBits (ir0x rs r1)) m
  -- Floating-point conversions
  | .Pfcvtds rd r1 => nextSet rs rd (Val.floatofsingle (rs r1)) m
  | .Pfcvtsd rd r1 => nextSet rs rd (Val.singleoffloat (rs r1)) m
  | .Pfcvtzs .W .S rd r1 => nextSet rs rd (Val.maketotal (Val.intofsingle (rs r1))) m
  | .Pfcvtzs .W .D rd r1 => nextSet rs rd (Val.maketotal (Val.intoffloat (rs r1))) m
  | .Pfcvtzs .X .S rd r1 => nextSet rs rd (Val.maketotal (Val.longofsingle (rs r1))) m
  | .Pfcvtzs .X .D rd r1 => nextSet rs rd (Val.maketotal (Val.longoffloat (rs r1))) m
  | .Pfcvtzu .W .S rd r1 => nextSet rs rd (Val.maketotal (Val.intuofsingle (rs r1))) m
  | .Pfcvtzu .W .D rd r1 => nextSet rs rd (Val.maketotal (Val.intuoffloat (rs r1))) m
  | .Pfcvtzu .X .S rd r1 => nextSet rs rd (Val.maketotal (Val.longuofsingle (rs r1))) m
  | .Pfcvtzu .X .D rd r1 => nextSet rs rd (Val.maketotal (Val.longuoffloat (rs r1))) m
  | .Pscvtf .S .W rd r1 => nextSet rs rd (Val.maketotal (Val.singleofint (rs r1))) m
  | .Pscvtf .D .W rd r1 => nextSet rs rd (Val.maketotal (Val.floatofint (rs r1))) m
  | .Pscvtf .S .X rd r1 => nextSet rs rd (Val.maketotal (Val.singleoflong (rs r1))) m
  | .Pscvtf .D .X rd r1 => nextSet rs rd (Val.maketotal (Val.floatoflong (rs r1))) m
  | .Pucvtf .S .W rd r1 => nextSet rs rd (Val.maketotal (Val.singleofintu (rs r1))) m
  | .Pucvtf .D .W rd r1 => nextSet rs rd (Val.maketotal (Val.floatofintu (rs r1))) m
  | .Pucvtf .S .X rd r1 => nextSet rs rd (Val.maketotal (Val.singleoflongu (rs r1))) m
  | .Pucvtf .D .X rd r1 => nextSet rs rd (Val.maketotal (Val.floatoflongu (rs r1))) m
  -- Floating-point arithmetic
  | .Pfabs .S rd r1 => nextSet rs rd (Val.absfs (rs r1)) m
  | .Pfabs .D rd r1 => nextSet rs rd (Val.absf (rs r1)) m
  | .Pfneg .S rd r1 => nextSet rs rd (Val.negfs (rs r1)) m
  | .Pfneg .D rd r1 => nextSet rs rd (Val.negf (rs r1)) m
  | .Pfadd .S rd r1 r2 => nextSet rs rd (Val.addfs (rs r1) (rs r2)) m
  | .Pfadd .D rd r1 r2 => nextSet rs rd (Val.addf (rs r1) (rs r2)) m
  | .Pfdiv .S rd r1 r2 => nextSet rs rd (Val.divfs (rs r1) (rs r2)) m
  | .Pfdiv .D rd r1 r2 => nextSet rs rd (Val.divf (rs r1) (rs r2)) m
  | .Pfmul .S rd r1 r2 => nextSet rs rd (Val.mulfs (rs r1) (rs r2)) m
  | .Pfmul .D rd r1 r2 => nextSet rs rd (Val.mulf (rs r1) (rs r2)) m
  | .Pfnmul .S rd r1 r2 => nextSet rs rd (Val.negfs (Val.mulfs (rs r1) (rs r2))) m
  | .Pfnmul .D rd r1 r2 => nextSet rs rd (Val.negf (Val.mulf (rs r1) (rs r2))) m
  | .Pfsub .S rd r1 r2 => nextSet rs rd (Val.subfs (rs r1) (rs r2)) m
  | .Pfsub .D rd r1 r2 => nextSet rs rd (Val.subf (rs r1) (rs r2)) m
  -- Floating-point comparison
  | .Pfcmp .S r1 r2 => .Next (nextinstr (compareSingle rs (rs r1) (rs r2))) m
  | .Pfcmp .D r1 r2 => .Next (nextinstr (compareFloat rs (rs r1) (rs r2))) m
  | .Pfcmp0 .S r1 => .Next (nextinstr (compareSingle rs (rs r1) (.Vsingle Floats.Float32.zero))) m
  | .Pfcmp0 .D r1 => .Next (nextinstr (compareFloat rs (rs r1) (.Vfloat Floats.Float.zero))) m
  -- Floating-point conditional select
  | .Pfsel rd r1 r2 cond => nextSet rs rd (selectCond cond rs (rs r1) (rs r2)) m
  -- Pseudo-instructions
  | .Pallocframe sz linkpos retaddrpos =>
      let (m1, stk) := Mem.alloc m 0 sz
      let sp := Val.Vptr stk Integers.Ptrofs.zero
      match Mem.storev .Mint64 m1 (Val.offsetPtr sp linkpos) (rs .SP) with
      | none => .Stuck
      | some m2 =>
          match Mem.storev .Mint64 m2 (Val.offsetPtr sp retaddrpos) (rs (.IR RA)) with
          | none => .Stuck
          | some m3 =>
              .Next (nextinstr (((rs.set (.IR .X15) (rs .SP)).set .SP sp).set (.IR .X16) .Vundef)) m3
  | .Pfreeframe sz pos =>
      match Mem.loadv .Mint64 m (Val.offsetPtr (rs .SP) pos) with
      | none => .Stuck
      | some v =>
          match rs .SP with
          | .Vptr stk _ =>
              match Mem.free m stk 0 sz with
              | none => .Stuck
              | some m' => .Next (nextinstr ((rs.set .SP v).set (.IR .X16) .Vundef)) m'
          | _ => .Stuck
  | .Plabel _ => .Next (nextinstr rs) m
  | .Ploadsymbol rd id => nextSet rs rd (Genv.symbolAddress ge id Integers.Ptrofs.zero) m
  | .Pcvtsw2x rd r1 => nextSet rs rd (Val.longofint (rs r1)) m
  | .Pcvtuw2x rd r1 => nextSet rs rd (Val.longofintu (rs r1)) m
  | .Pcvtx2w rd => nextSet rs rd (Val.loword (rs rd)) m
  | .Pbtbl r tbl =>
      match (rs.set (.IR .X16) .Vundef) r with
      | .Vint n =>
          match CminorSel.listNthZ tbl (Integers.Int.unsigned n) with
          | none => .Stuck
          | some lbl => gotoLabel f lbl (rs.set (.IR .X16) .Vundef) m
      | _ => .Stuck
  | .Pcfi_rel_offset _ => .Next (nextinstr rs) m
  | .Pbuiltin .. => .Stuck
  -- Not generated by Asmgen, not modeled
  | .Pldp .. | .Pstp .. | .Pcls .. | .Pclz .. | .Prev .. | .Prev16 .. | .Prbit ..
  | .Pfsqrt .. | .Pfmadd .. | .Pfmsub .. | .Pfnmadd .. | .Pfnmsub .. | .Pfmax ..
  | .Pfmin .. | .Pnop | .Pcfi_adjust .. => .Stuck

/-- `Asm.preg_of` -/
def pregOf (r : Mreg) : Preg :=
  match r with
  | .R0 => .IR .X0 | .R1 => .IR .X1 | .R2 => .IR .X2 | .R3 => .IR .X3
  | .R4 => .IR .X4 | .R5 => .IR .X5 | .R6 => .IR .X6 | .R7 => .IR .X7
  | .R8 => .IR .X8 | .R9 => .IR .X9 | .R10 => .IR .X10 | .R11 => .IR .X11
  | .R12 => .IR .X12 | .R13 => .IR .X13 | .R14 => .IR .X14 | .R15 => .IR .X15
  | .R17 => .IR .X17 | .R19 => .IR .X19
  | .R20 => .IR .X20 | .R21 => .IR .X21 | .R22 => .IR .X22 | .R23 => .IR .X23
  | .R24 => .IR .X24 | .R25 => .IR .X25 | .R26 => .IR .X26 | .R27 => .IR .X27
  | .R28 => .IR .X28 | .R29 => .IR .X29
  | .F0 => .FR .D0 | .F1 => .FR .D1 | .F2 => .FR .D2 | .F3 => .FR .D3
  | .F4 => .FR .D4 | .F5 => .FR .D5 | .F6 => .FR .D6 | .F7 => .FR .D7
  | .F8 => .FR .D8 | .F9 => .FR .D9 | .F10 => .FR .D10 | .F11 => .FR .D11
  | .F12 => .FR .D12 | .F13 => .FR .D13 | .F14 => .FR .D14 | .F15 => .FR .D15
  | .F16 => .FR .D16 | .F17 => .FR .D17 | .F18 => .FR .D18 | .F19 => .FR .D19
  | .F20 => .FR .D20 | .F21 => .FR .D21 | .F22 => .FR .D22 | .F23 => .FR .D23
  | .F24 => .FR .D24 | .F25 => .FR .D25 | .F26 => .FR .D26 | .F27 => .FR .D27
  | .F28 => .FR .D28 | .F29 => .FR .D29 | .F30 => .FR .D30 | .F31 => .FR .D31

/-- `Asm.undef_caller_save_regs` -/
def undefCallerSaveRegs (rs : Regset) : Regset := fun r =>
  if decide (r = .SP) || decide (r ∈ ((Mreg.allMregs.filter isCalleeSave).map pregOf)) then rs r
  else .Vundef

/-- `Asm.extcall_arg` -/
inductive ExtcallArg (rs : Regset) (m : Mem) : Loc → Val → Prop where
  | reg (r) : ExtcallArg rs m (.R r) (rs (pregOf r))
  | stack (ofs ty bofs v) :
      bofs = Stacklayout.feOfsArg + 4 * ofs →
      Mem.loadv (Chunk.ofTyp ty) m (Val.offsetPtr (rs .SP) (Integers.Ptrofs.repr bofs)) = some v →
      ExtcallArg rs m (.S .Outgoing ofs ty) v

/-- `Asm.extcall_arg_pair` -/
inductive ExtcallArgPair (rs : Regset) (m : Mem) : RPair Loc → Val → Prop where
  | one (l v) : ExtcallArg rs m l v → ExtcallArgPair rs m (.One l) v
  | twolong (hi lo vhi vlo) :
      ExtcallArg rs m hi vhi → ExtcallArg rs m lo vlo →
      ExtcallArgPair rs m (.Twolong hi lo) (Val.longofwords vhi vlo)

/-- `Asm.extcall_arguments` -/
def ExtcallArguments (abi : AbiKind) (rs : Regset) (m : Mem) (sg : Signature)
    (args : List Val) : Prop :=
  ListForall2 (ExtcallArgPair rs m) (locArguments abi sg) args

/-- `Asm.loc_external_result` -/
def locExternalResult (sg : Signature) : RPair Preg := RPair.map pregOf (locResult sg)

/-- `Asm.state` -/
inductive State where
  | State (rs : Regset) (m : Mem)

variable (abi : AbiKind)

/-- `Asm.step` -/
inductive Step : State → Trace → State → Prop where
  | exec_step_internal (b ofs f i rs m rs' m') :
      rs .PC = .Vptr b ofs →
      Genv.findFunctPtr ge b = some (.Internal f) →
      findInstr (Integers.Ptrofs.unsigned ofs) f.fn_code = some i →
      execInstr sym ge f i rs m = .Next rs' m' →
      Step (.State rs m) E0 (.State rs' m')
  | exec_step_builtin (b ofs f ef args res rs m vargs t vres rs' m') :
      rs .PC = .Vptr b ofs →
      Genv.findFunctPtr ge b = some (.Internal f) →
      findInstr (Integers.Ptrofs.unsigned ofs) f.fn_code = some (.Pbuiltin ef args res) →
      EvalBuiltinArgs ge.toSenv rs (rs .SP) m args vargs →
      externalCall ef ge.toSenv vargs m t vres m' →
      rs' = nextinstr (setRes res vres
        (undefRegs (.IR .X16 :: .IR .X30 :: (destroyedByBuiltin ef).map pregOf) rs)) →
      Step (.State rs m) t (.State rs' m')
  | exec_step_external (b ef args res rs m t rs' m') :
      rs .PC = .Vptr b Integers.Ptrofs.zero →
      Genv.findFunctPtr ge b = some (.External ef) →
      externalCall ef ge.toSenv args m t res m' →
      ExtcallArguments abi rs m ef.sig args →
      rs' = (setPair (locExternalResult ef.sig) res (undefCallerSaveRegs rs)).set .PC (rs (.IR RA)) →
      Step (.State rs m) t (.State rs' m')

end RELSEM

/-- `Asm.initial_state` -/
inductive InitialState (p : Program) : State → Prop where
  | intro (m0) :
      p.initMem = some m0 →
      InitialState p (.State
        (((Regset.init .Vundef).set .PC
          (Genv.symbolAddress p.globalenv p.prog_main Integers.Ptrofs.zero)).set
          (.IR RA) Val.Vnullptr |>.set .SP Val.Vnullptr) m0)

/-- `Asm.final_state` -/
inductive FinalState : State → Integers.Int → Prop where
  | intro (rs m r) :
      rs .PC = Val.Vnullptr →
      rs (.IR .X0) = .Vint r →
      FinalState (.State rs m) r

/-- `Asm.semantics` -/
def semantics (sym : SymbolSplit) (abi : AbiKind) (p : Program) : Semantics where
  state := State
  step := Step sym p.globalenv abi
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
theorem extcallArguments_determ {abi rs m sg args1 args2}
    (h1 : ExtcallArguments abi rs m sg args1) (h2 : ExtcallArguments abi rs m sg args2) :
    args1 = args2 := by
  unfold ExtcallArguments at h1 h2
  generalize locArguments abi sg = l at h1 h2
  induction h1 generalizing args2 with
  | nil => cases h2; rfl
  | cons ha _ ih => cases h2 with
    | cons hb hl => rw [extcallArgPair_determ ha hb, ih hl]

/-- `Asm.data_preg` -/
def dataPreg (r : Preg) : Bool :=
  match r with
  | .IR .X16 => false
  | .IR .X30 => false
  | .IR _ => true
  | .FR _ => true
  | .CR _ => false
  | .SP => true
  | .PC => false

end Asm
end CC
