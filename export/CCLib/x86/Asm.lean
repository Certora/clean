/-
  Abstract syntax and semantics for x86 assembly language — port of
  `x86/Asm.v` (`fe_ofs_arg` comes from `CCLib.x86.Stacklayout`).

  Ported: registers (`ireg`, `freg`, `crbit`, `preg`), `addrmode`,
  `testcond`, the instruction set, `function`, `fundef`, `program`, register
  sets and their operations (`undef_regs`, `set_pair`, `set_res`),
  `find_instr`, `is_label`, `label_pos`, `eval_addrmode32/64`,
  `compare_ints`, `compare_longs`, `compare_floats`, `compare_floats32`,
  `eval_testcond`, `outcome`, `nextinstr`, `nextinstr_nf`, `goto_label`,
  `exec_load`, `exec_store`, `exec_instr`, `preg_of`,
  `undef_caller_save_regs`, `extcall_arg`, `extcall_arg_pair`,
  `extcall_arguments`, `loc_external_result`, `state`, `step`,
  `initial_state`, `final_state`, `semantics`, `extcall_arguments_determ`,
  `data_preg`.

  Differences from Rocq:
  * `Archi.win64` is an explicit argument `win64` (it determines the
    calling convention and `fe_ofs_arg`).
  * The coercions `ireg >-> preg`, … are `Coe` instances; `Pregmap.t val` is
    the function type `Preg → Val`.
  * `semantics_determinate` is not ported (as for aarch64).
-/
import CCLib.backend.Mach
import CCLib.x86.Op
import CCLib.x86.Conventions
import CCLib.x86.Stacklayout

namespace CC
namespace X86


namespace Asm

open Smallstep CC.X86.Conventions1

/-! ## Abstract syntax -/

/-- `Asm.ireg` -/
inductive Ireg where
  | RAX | RBX | RCX | RDX | RSI | RDI | RBP | RSP
  | R8 | R9 | R10 | R11 | R12 | R13 | R14 | R15
  deriving DecidableEq, Repr

/-- `Asm.freg` (SSE registers) -/
inductive Freg where
  | XMM0 | XMM1 | XMM2 | XMM3 | XMM4 | XMM5 | XMM6 | XMM7
  | XMM8 | XMM9 | XMM10 | XMM11 | XMM12 | XMM13 | XMM14 | XMM15
  deriving DecidableEq, Repr

/-- `Asm.crbit`: bits of the flags register. -/
inductive Crbit where
  | ZF | CF | PF | SF | OF
  deriving DecidableEq, Repr

/-- `Asm.preg` -/
inductive Preg where
  /-- program counter -/
  | PC
  /-- integer register -/
  | IR (r : Ireg)
  /-- XMM register -/
  | FR (r : Freg)
  /-- top of the x87 stack -/
  | ST0
  /-- bit of the flags register -/
  | CR (r : Crbit)
  /-- pseudo-register holding the return address -/
  | RA
  deriving DecidableEq, Repr

instance : Coe Ireg Preg := ⟨.IR⟩
instance : Coe Freg Preg := ⟨.FR⟩
instance : Coe Crbit Preg := ⟨.CR⟩

/-- The stack pointer `SP` = `RSP`. -/
abbrev SP : Ireg := .RSP

/-- `Asm.label` -/
abbrev Label := Positive

/-- `Asm.addrmode`: `base + index * scale + displacement`, where the
displacement is an integer or `symbol + offset`. -/
inductive Addrmode where
  | Addrmode (base : Option Ireg) (ofs : Option (Ireg × Z)) (const : Z ⊕ (Ident × Integers.Ptrofs))

/-- `Asm.testcond` -/
inductive Testcond where
  | Cond_e | Cond_ne
  | Cond_b | Cond_be | Cond_ae | Cond_a
  | Cond_l | Cond_le | Cond_ge | Cond_g
  | Cond_p | Cond_np
  deriving DecidableEq, Repr

/-- `Asm.instruction` -/
inductive Instruction where
  -- Moves
  | Pmov_rr (rd : Ireg) (r1 : Ireg)
  | Pmovl_ri (rd : Ireg) (n : Integers.Int)
  | Pmovq_ri (rd : Ireg) (n : Integers.Int64)
  | Pmov_rs (rd : Ireg) (id : Ident)
  | Pmovl_rm (rd : Ireg) (a : Addrmode)
  | Pmovq_rm (rd : Ireg) (a : Addrmode)
  | Pmovl_mr (a : Addrmode) (rs : Ireg)
  | Pmovq_mr (a : Addrmode) (rs : Ireg)
  | Pmovsd_ff (rd : Freg) (r1 : Freg)
  | Pmovsd_fi (rd : Freg) (n : Floats.Float)
  | Pmovsd_fm (rd : Freg) (a : Addrmode)
  | Pmovsd_mf (a : Addrmode) (r1 : Freg)
  | Pmovss_fi (rd : Freg) (n : Floats.Float32)
  | Pmovss_fm (rd : Freg) (a : Addrmode)
  | Pmovss_mf (a : Addrmode) (r1 : Freg)
  | Pfldl_m (a : Addrmode)
  | Pfstpl_m (a : Addrmode)
  | Pflds_m (a : Addrmode)
  | Pfstps_m (a : Addrmode)
  -- Moves with conversion
  | Pmovb_mr (a : Addrmode) (rs : Ireg)
  | Pmovw_mr (a : Addrmode) (rs : Ireg)
  | Pmovzb_rr (rd : Ireg) (rs : Ireg)
  | Pmovzb_rm (rd : Ireg) (a : Addrmode)
  | Pmovsb_rr (rd : Ireg) (rs : Ireg)
  | Pmovsb_rm (rd : Ireg) (a : Addrmode)
  | Pmovzw_rr (rd : Ireg) (rs : Ireg)
  | Pmovzw_rm (rd : Ireg) (a : Addrmode)
  | Pmovsw_rr (rd : Ireg) (rs : Ireg)
  | Pmovsw_rm (rd : Ireg) (a : Addrmode)
  | Pmovzl_rr (rd : Ireg) (rs : Ireg)
  | Pmovsl_rr (rd : Ireg) (rs : Ireg)
  | Pmovls_rr (rd : Ireg)
  | Pcvtsd2ss_ff (rd : Freg) (r1 : Freg)
  | Pcvtss2sd_ff (rd : Freg) (r1 : Freg)
  | Pcvttsd2si_rf (rd : Ireg) (r1 : Freg)
  | Pcvtsi2sd_fr (rd : Freg) (r1 : Ireg)
  | Pcvttss2si_rf (rd : Ireg) (r1 : Freg)
  | Pcvtsi2ss_fr (rd : Freg) (r1 : Ireg)
  | Pcvttsd2sl_rf (rd : Ireg) (r1 : Freg)
  | Pcvtsl2sd_fr (rd : Freg) (r1 : Ireg)
  | Pcvttss2sl_rf (rd : Ireg) (r1 : Freg)
  | Pcvtsl2ss_fr (rd : Freg) (r1 : Ireg)
  -- Integer arithmetic
  | Pleal (rd : Ireg) (a : Addrmode)
  | Pleaq (rd : Ireg) (a : Addrmode)
  | Pnegl (rd : Ireg)
  | Pnegq (rd : Ireg)
  | Paddl_ri (rd : Ireg) (n : Integers.Int)
  | Paddq_ri (rd : Ireg) (n : Integers.Int64)
  | Psubl_rr (rd : Ireg) (r1 : Ireg)
  | Psubq_rr (rd : Ireg) (r1 : Ireg)
  | Pimull_rr (rd : Ireg) (r1 : Ireg)
  | Pimulq_rr (rd : Ireg) (r1 : Ireg)
  | Pimull_ri (rd : Ireg) (n : Integers.Int)
  | Pimulq_ri (rd : Ireg) (n : Integers.Int64)
  | Pimull_r (r1 : Ireg)
  | Pimulq_r (r1 : Ireg)
  | Pmull_r (r1 : Ireg)
  | Pmulq_r (r1 : Ireg)
  | Pcltd
  | Pcqto
  | Pdivl (r1 : Ireg)
  | Pdivq (r1 : Ireg)
  | Pidivl (r1 : Ireg)
  | Pidivq (r1 : Ireg)
  | Pandl_rr (rd : Ireg) (r1 : Ireg)
  | Pandq_rr (rd : Ireg) (r1 : Ireg)
  | Pandl_ri (rd : Ireg) (n : Integers.Int)
  | Pandq_ri (rd : Ireg) (n : Integers.Int64)
  | Porl_rr (rd : Ireg) (r1 : Ireg)
  | Porq_rr (rd : Ireg) (r1 : Ireg)
  | Porl_ri (rd : Ireg) (n : Integers.Int)
  | Porq_ri (rd : Ireg) (n : Integers.Int64)
  | Pxorl_r (rd : Ireg)
  | Pxorq_r (rd : Ireg)
  | Pxorl_rr (rd : Ireg) (r1 : Ireg)
  | Pxorq_rr (rd : Ireg) (r1 : Ireg)
  | Pxorl_ri (rd : Ireg) (n : Integers.Int)
  | Pxorq_ri (rd : Ireg) (n : Integers.Int64)
  | Pnotl (rd : Ireg)
  | Pnotq (rd : Ireg)
  | Psall_rcl (rd : Ireg)
  | Psalq_rcl (rd : Ireg)
  | Psall_ri (rd : Ireg) (n : Integers.Int)
  | Psalq_ri (rd : Ireg) (n : Integers.Int)
  | Pshrl_rcl (rd : Ireg)
  | Pshrq_rcl (rd : Ireg)
  | Pshrl_ri (rd : Ireg) (n : Integers.Int)
  | Pshrq_ri (rd : Ireg) (n : Integers.Int)
  | Psarl_rcl (rd : Ireg)
  | Psarq_rcl (rd : Ireg)
  | Psarl_ri (rd : Ireg) (n : Integers.Int)
  | Psarq_ri (rd : Ireg) (n : Integers.Int)
  | Pshld_ri (rd : Ireg) (r1 : Ireg) (n : Integers.Int)
  | Prorl_ri (rd : Ireg) (n : Integers.Int)
  | Prorq_ri (rd : Ireg) (n : Integers.Int)
  | Pcmpl_rr (r1 r2 : Ireg)
  | Pcmpq_rr (r1 r2 : Ireg)
  | Pcmpl_ri (r1 : Ireg) (n : Integers.Int)
  | Pcmpq_ri (r1 : Ireg) (n : Integers.Int64)
  | Ptestl_rr (r1 r2 : Ireg)
  | Ptestq_rr (r1 r2 : Ireg)
  | Ptestl_ri (r1 : Ireg) (n : Integers.Int)
  | Ptestq_ri (r1 : Ireg) (n : Integers.Int64)
  | Pcmov (c : Testcond) (rd : Ireg) (r1 : Ireg)
  | Psetcc (c : Testcond) (rd : Ireg)
  -- Floating-point arithmetic
  | Paddd_ff (rd : Freg) (r1 : Freg)
  | Psubd_ff (rd : Freg) (r1 : Freg)
  | Pmuld_ff (rd : Freg) (r1 : Freg)
  | Pdivd_ff (rd : Freg) (r1 : Freg)
  | Pnegd (rd : Freg)
  | Pabsd (rd : Freg)
  | Pcomisd_ff (r1 r2 : Freg)
  | Pxorpd_f (rd : Freg)
  | Padds_ff (rd : Freg) (r1 : Freg)
  | Psubs_ff (rd : Freg) (r1 : Freg)
  | Pmuls_ff (rd : Freg) (r1 : Freg)
  | Pdivs_ff (rd : Freg) (r1 : Freg)
  | Pnegs (rd : Freg)
  | Pabss (rd : Freg)
  | Pcomiss_ff (r1 r2 : Freg)
  | Pxorps_f (rd : Freg)
  -- Branches and calls
  | Pjmp_l (l : Label)
  | Pjmp_s (symb : Ident) (sg : Signature)
  | Pjmp_r (r : Ireg) (sg : Signature)
  | Pjcc (c : Testcond) (l : Label)
  | Pjcc2 (c1 c2 : Testcond) (l : Label)
  | Pjmptbl (r : Ireg) (tbl : List Label)
  | Pcall_s (symb : Ident) (sg : Signature)
  | Pcall_r (r : Ireg) (sg : Signature)
  | Pret
  -- Saving and restoring registers
  | Pmov_rm_a (rd : Ireg) (a : Addrmode)
  | Pmov_mr_a (a : Addrmode) (rs : Ireg)
  | Pmovsd_fm_a (rd : Freg) (a : Addrmode)
  | Pmovsd_mf_a (a : Addrmode) (r1 : Freg)
  -- Pseudo-instructions
  | Plabel (l : Label)
  | Pallocframe (sz : Z) (ofs_ra ofs_link : Integers.Ptrofs)
  | Pfreeframe (sz : Z) (ofs_ra ofs_link : Integers.Ptrofs)
  | Pbuiltin (ef : ExtFun) (args : List (BuiltinArg Preg)) (res : BuiltinRes Preg)
  -- Instructions not generated by `Asmgen`
  | Padcl_ri (rd : Ireg) (n : Integers.Int)
  | Padcl_rr (rd : Ireg) (r2 : Ireg)
  | Paddl_mi (a : Addrmode) (n : Integers.Int)
  | Paddl_rr (rd : Ireg) (r2 : Ireg)
  | Pbsfl (rd : Ireg) (r1 : Ireg)
  | Pbsfq (rd : Ireg) (r1 : Ireg)
  | Pbsrl (rd : Ireg) (r1 : Ireg)
  | Pbsrq (rd : Ireg) (r1 : Ireg)
  | Pbswap64 (rd : Ireg)
  | Pbswap32 (rd : Ireg)
  | Pbswap16 (rd : Ireg)
  | Pcfi_adjust (n : Integers.Int)
  | Pfmadd132 (rd : Freg) (r2 : Freg) (r3 : Freg)
  | Pfmadd213 (rd : Freg) (r2 : Freg) (r3 : Freg)
  | Pfmadd231 (rd : Freg) (r2 : Freg) (r3 : Freg)
  | Pfmsub132 (rd : Freg) (r2 : Freg) (r3 : Freg)
  | Pfmsub213 (rd : Freg) (r2 : Freg) (r3 : Freg)
  | Pfmsub231 (rd : Freg) (r2 : Freg) (r3 : Freg)
  | Pfnmadd132 (rd : Freg) (r2 : Freg) (r3 : Freg)
  | Pfnmadd213 (rd : Freg) (r2 : Freg) (r3 : Freg)
  | Pfnmadd231 (rd : Freg) (r2 : Freg) (r3 : Freg)
  | Pfnmsub132 (rd : Freg) (r2 : Freg) (r3 : Freg)
  | Pfnmsub213 (rd : Freg) (r2 : Freg) (r3 : Freg)
  | Pfnmsub231 (rd : Freg) (r2 : Freg) (r3 : Freg)
  | Pmaxsd (rd : Freg) (r2 : Freg)
  | Pminsd (rd : Freg) (r2 : Freg)
  | Pmovb_rm (rd : Ireg) (a : Addrmode)
  | Pmovq_rf (rd : Ireg) (r1 : Freg)
  | Pmovsq_mr (a : Addrmode) (rs : Freg)
  | Pmovsq_rm (rd : Freg) (a : Addrmode)
  | Pmovsb
  | Pmovsw
  | Pmovw_rm (rd : Ireg) (ad : Addrmode)
  | Pnop
  | Prep_movsl
  | Psbbl_rr (rd : Ireg) (r2 : Ireg)
  | Psqrtsd (rd : Freg) (r1 : Freg)
  | Psubl_ri (rd : Ireg) (n : Integers.Int)
  | Psubq_ri (rd : Ireg) (n : Integers.Int64)

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

/-- `Asm.undef_regs` -/
def undefRegs : List Preg → Regset → Regset
  | [], rs => rs
  | r :: l', rs => undefRegs l' (rs.set r .Vundef)

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

section RELSEM
variable (ge : CGenv)

/-- `Asm.eval_addrmode32` -/
def evalAddrmode32 (a : Addrmode) (rs : Regset) : Val :=
  match a with
  | .Addrmode base ofs const =>
    Val.add
      (match base with
       | none => .Vint Integers.Int.zero
       | some r => rs r)
      (Val.add
        (match ofs with
         | none => .Vint Integers.Int.zero
         | some (r, sc) =>
            if sc = 1 then rs r else Val.mul (rs r) (.Vint (Integers.Int.repr sc)))
        (match const with
         | .inl ofs => .Vint (Integers.Int.repr ofs)
         | .inr (id, ofs) => Genv.symbolAddress ge id ofs))

/-- `Asm.eval_addrmode64` -/
def evalAddrmode64 (a : Addrmode) (rs : Regset) : Val :=
  match a with
  | .Addrmode base ofs const =>
    Val.addl
      (match base with
       | none => .Vlong Integers.Int64.zero
       | some r => rs r)
      (Val.addl
        (match ofs with
         | none => .Vlong Integers.Int64.zero
         | some (r, sc) =>
            if sc = 1 then rs r else Val.mull (rs r) (.Vlong (Integers.Int64.repr sc)))
        (match const with
         | .inl ofs => .Vlong (Integers.Int64.repr ofs)
         | .inr (id, ofs) => Genv.symbolAddress ge id ofs))

/-- `Asm.eval_addrmode` -/
def evalAddrmode (a : Addrmode) (rs : Regset) : Val :=
  if Archi.ptr64 then evalAddrmode64 ge a rs else evalAddrmode32 ge a rs

end RELSEM

/-- `Asm.compare_ints`: `ZF`, `CF`, `SF`, `OF` as set by `cmp`; `PF` is
undefined. -/
def compareInts (x y : Val) (rs : Regset) (m : Mem) : Regset :=
  ((((rs.set (.CR .ZF) (Val.cmpu (Mem.validPointer m) .Ceq x y)).set
    (.CR .CF) (Val.cmpu (Mem.validPointer m) .Clt x y)).set
    (.CR .SF) (Val.negative (Val.sub x y))).set
    (.CR .OF) (Val.sub_overflow x y)).set
    (.CR .PF) .Vundef

/-- `Asm.compare_longs` -/
def compareLongs (x y : Val) (rs : Regset) (m : Mem) : Regset :=
  ((((rs.set (.CR .ZF) (Val.maketotal (Val.cmplu (Mem.validPointer m) .Ceq x y))).set
    (.CR .CF) (Val.maketotal (Val.cmplu (Mem.validPointer m) .Clt x y))).set
    (.CR .SF) (Val.negativel (Val.subl x y))).set
    (.CR .OF) (Val.subl_overflow x y)).set
    (.CR .PF) .Vundef

/-- The flags set by `comisd` / `comiss`. -/
def flagRegs : List Preg := [.CR .ZF, .CR .CF, .CR .PF, .CR .SF, .CR .OF]

/-- `Asm.compare_floats` (`comisd`): `ZF`, `CF`, `PF` describe the
comparison (all set if unordered); `SF`, `OF` are undefined. -/
def compareFloats (vx vy : Val) (rs : Regset) : Regset :=
  match vx, vy with
  | .Vfloat x, .Vfloat y =>
      ((((rs.set (.CR .ZF)
          (Val.ofBool (Floats.Float.cmp .Ceq x y || !Floats.Float.ordered x y))).set
        (.CR .CF) (Val.ofBool (!Floats.Float.cmp .Cge x y))).set
        (.CR .PF) (Val.ofBool (!Floats.Float.ordered x y))).set
        (.CR .SF) .Vundef).set
        (.CR .OF) .Vundef
  | _, _ => undefRegs flagRegs rs

/-- `Asm.compare_floats32` (`comiss`) -/
def compareFloats32 (vx vy : Val) (rs : Regset) : Regset :=
  match vx, vy with
  | .Vsingle x, .Vsingle y =>
      ((((rs.set (.CR .ZF)
          (Val.ofBool (Floats.Float32.cmp .Ceq x y || !Floats.Float32.ordered x y))).set
        (.CR .CF) (Val.ofBool (!Floats.Float32.cmp .Cge x y))).set
        (.CR .PF) (Val.ofBool (!Floats.Float32.ordered x y))).set
        (.CR .SF) .Vundef).set
        (.CR .OF) .Vundef
  | _, _ => undefRegs flagRegs rs

/-- `Asm.eval_testcond` -/
def evalTestcond (c : Testcond) (rs : Regset) : Option Bool :=
  let isOne (n : Integers.Int) := Integers.Int.eq n Integers.Int.one
  let isZero (n : Integers.Int) := Integers.Int.eq n Integers.Int.zero
  match c with
  | .Cond_e => match rs (.CR .ZF) with | .Vint n => some (isOne n) | _ => none
  | .Cond_ne => match rs (.CR .ZF) with | .Vint n => some (isZero n) | _ => none
  | .Cond_b => match rs (.CR .CF) with | .Vint n => some (isOne n) | _ => none
  | .Cond_be =>
      match rs (.CR .CF), rs (.CR .ZF) with
      | .Vint c, .Vint z => some (isOne c || isOne z)
      | _, _ => none
  | .Cond_ae => match rs (.CR .CF) with | .Vint n => some (isZero n) | _ => none
  | .Cond_a =>
      match rs (.CR .CF), rs (.CR .ZF) with
      | .Vint c, .Vint z => some (isZero c && isZero z)
      | _, _ => none
  | .Cond_l =>
      match rs (.CR .OF), rs (.CR .SF) with
      | .Vint o, .Vint s => some (isOne (Integers.Int.xor o s))
      | _, _ => none
  | .Cond_le =>
      match rs (.CR .OF), rs (.CR .SF), rs (.CR .ZF) with
      | .Vint o, .Vint s, .Vint z => some (isOne (Integers.Int.xor o s) || isOne z)
      | _, _, _ => none
  | .Cond_ge =>
      match rs (.CR .OF), rs (.CR .SF) with
      | .Vint o, .Vint s => some (isZero (Integers.Int.xor o s))
      | _, _ => none
  | .Cond_g =>
      match rs (.CR .OF), rs (.CR .SF), rs (.CR .ZF) with
      | .Vint o, .Vint s, .Vint z => some (isZero (Integers.Int.xor o s) && isZero z)
      | _, _, _ => none
  | .Cond_p => match rs (.CR .PF) with | .Vint n => some (isOne n) | _ => none
  | .Cond_np => match rs (.CR .PF) with | .Vint n => some (isZero n) | _ => none

/-- `Asm.outcome` -/
inductive Outcome where
  | Next (rs : Regset) (m : Mem)
  | Stuck

/-- `Asm.nextinstr` -/
def nextinstr (rs : Regset) : Regset :=
  rs.set .PC (Val.offsetPtr (rs .PC) Integers.Ptrofs.one)

/-- `Asm.nextinstr_nf`: also sets the condition flags to `Vundef`. -/
def nextinstrNf (rs : Regset) : Regset :=
  nextinstr (undefRegs flagRegs rs)

/-- `Asm.goto_label` -/
def gotoLabel (f : Function) (lbl : Label) (rs : Regset) (m : Mem) : Outcome :=
  match labelPos lbl 0 f.fn_code with
  | none => .Stuck
  | some pos =>
      match rs .PC with
      | .Vptr b _ => .Next (rs.set .PC (.Vptr b (Integers.Ptrofs.repr pos))) m
      | _ => .Stuck

section RELSEM
variable (ge : CGenv)

/-- `Asm.exec_load` -/
def execLoad (chunk : Chunk) (m : Mem) (a : Addrmode) (rs : Regset) (rd : Preg) : Outcome :=
  match Mem.loadv chunk m (evalAddrmode ge a rs) with
  | some v => .Next (nextinstrNf (rs.set rd v)) m
  | none => .Stuck

/-- `Asm.exec_store` -/
def execStore (chunk : Chunk) (m : Mem) (a : Addrmode) (rs : Regset) (r1 : Preg)
    (destroyed : List Preg) : Outcome :=
  match Mem.storev chunk m (evalAddrmode ge a rs) (rs r1) with
  | some m' => .Next (nextinstrNf (undefRegs destroyed rs)) m'
  | none => .Stuck

/-- `Next (nextinstr (rs # rd <- v)) m` -/
abbrev nextSet (rs : Regset) (rd : Preg) (v : Val) (m : Mem) : Outcome :=
  .Next (nextinstr (rs.set rd v)) m

/-- `Next (nextinstr_nf (rs # rd <- v)) m` -/
abbrev nextSetNf (rs : Regset) (rd : Preg) (v : Val) (m : Mem) : Outcome :=
  .Next (nextinstrNf (rs.set rd v)) m

/-- The double-width division instructions (`div`, `idiv`): divide
`RDX:RAX` by `r1`, quotient in `RAX` and remainder in `RDX`. -/
def execDiv {T : Type} (proj : Val → Option T) (inj : T → Val)
    (divmod : T → T → T → Option (T × T)) (r1 : Ireg) (rs : Regset) (m : Mem) : Outcome :=
  match proj (rs (.IR .RDX)), proj (rs (.IR .RAX)), proj (rs (.IR r1)) with
  | some nh, some nl, some d =>
      match divmod nh nl d with
      | some (q, r) => .Next (nextinstrNf ((rs.set (.IR .RAX) (inj q)).set (.IR .RDX) (inj r))) m
      | none => .Stuck
  | _, _, _ => .Stuck

/-- The 32-bit integer contained in a value, if any. -/
def projInt : Val → Option Integers.Int
  | .Vint n => some n
  | _ => none

/-- The 64-bit integer contained in a value, if any. -/
def projLong : Val → Option Integers.Int64
  | .Vlong n => some n
  | _ => none

/-- `Asm.exec_instr` -/
def execInstr (f : Function) (i : Instruction) (rs : Regset) (m : Mem) : Outcome :=
  let load := execLoad ge
  let store := execStore ge
  match i with
  -- Moves
  | .Pmov_rr rd r1 => nextSet rs rd (rs r1) m
  | .Pmovl_ri rd n => nextSetNf rs rd (.Vint n) m
  | .Pmovq_ri rd n => nextSetNf rs rd (.Vlong n) m
  | .Pmov_rs rd id => nextSetNf rs rd (Genv.symbolAddress ge id Integers.Ptrofs.zero) m
  | .Pmovl_rm rd a => load .Mint32 m a rs rd
  | .Pmovq_rm rd a => load .Mint64 m a rs rd
  | .Pmovl_mr a r1 => store .Mint32 m a rs r1 []
  | .Pmovq_mr a r1 => store .Mint64 m a rs r1 []
  | .Pmovsd_ff rd r1 => nextSet rs rd (rs r1) m
  | .Pmovsd_fi rd n => nextSet rs rd (.Vfloat n) m
  | .Pmovsd_fm rd a => load .Mfloat64 m a rs rd
  | .Pmovsd_mf a r1 => store .Mfloat64 m a rs r1 []
  | .Pmovss_fi rd n => nextSet rs rd (.Vsingle n) m
  | .Pmovss_fm rd a => load .Mfloat32 m a rs rd
  | .Pmovss_mf a r1 => store .Mfloat32 m a rs r1 []
  | .Pfldl_m a => load .Mfloat64 m a rs .ST0
  | .Pfstpl_m a => store .Mfloat64 m a rs .ST0 [.ST0]
  | .Pflds_m a => load .Mfloat32 m a rs .ST0
  | .Pfstps_m a => store .Mfloat32 m a rs .ST0 [.ST0]
  -- Moves with conversion
  | .Pmovb_mr a r1 => store .Mint8unsigned m a rs r1 []
  | .Pmovw_mr a r1 => store .Mint16unsigned m a rs r1 []
  | .Pmovzb_rr rd r1 => nextSet rs rd (Val.zeroExt 8 (rs r1)) m
  | .Pmovzb_rm rd a => load .Mint8unsigned m a rs rd
  | .Pmovsb_rr rd r1 => nextSet rs rd (Val.signExt 8 (rs r1)) m
  | .Pmovsb_rm rd a => load .Mint8signed m a rs rd
  | .Pmovzw_rr rd r1 => nextSet rs rd (Val.zeroExt 16 (rs r1)) m
  | .Pmovzw_rm rd a => load .Mint16unsigned m a rs rd
  | .Pmovsw_rr rd r1 => nextSet rs rd (Val.signExt 16 (rs r1)) m
  | .Pmovsw_rm rd a => load .Mint16signed m a rs rd
  | .Pmovzl_rr rd r1 => nextSet rs rd (Val.longofintu (rs r1)) m
  | .Pmovsl_rr rd r1 => nextSet rs rd (Val.longofint (rs r1)) m
  | .Pmovls_rr rd => nextSet rs rd (Val.loword (rs rd)) m
  | .Pcvtsd2ss_ff rd r1 => nextSet rs rd (Val.singleoffloat (rs r1)) m
  | .Pcvtss2sd_ff rd r1 => nextSet rs rd (Val.floatofsingle (rs r1)) m
  | .Pcvttsd2si_rf rd r1 => nextSet rs rd (Val.maketotal (Val.intoffloat (rs r1))) m
  | .Pcvtsi2sd_fr rd r1 => nextSet rs rd (Val.maketotal (Val.floatofint (rs r1))) m
  | .Pcvttss2si_rf rd r1 => nextSet rs rd (Val.maketotal (Val.intofsingle (rs r1))) m
  | .Pcvtsi2ss_fr rd r1 => nextSet rs rd (Val.maketotal (Val.singleofint (rs r1))) m
  | .Pcvttsd2sl_rf rd r1 => nextSet rs rd (Val.maketotal (Val.longoffloat (rs r1))) m
  | .Pcvtsl2sd_fr rd r1 => nextSet rs rd (Val.maketotal (Val.floatoflong (rs r1))) m
  | .Pcvttss2sl_rf rd r1 => nextSet rs rd (Val.maketotal (Val.longofsingle (rs r1))) m
  | .Pcvtsl2ss_fr rd r1 => nextSet rs rd (Val.maketotal (Val.singleoflong (rs r1))) m
  -- Integer arithmetic
  | .Pleal rd a => nextSet rs rd (evalAddrmode32 ge a rs) m
  | .Pleaq rd a => nextSet rs rd (evalAddrmode64 ge a rs) m
  | .Pnegl rd => nextSetNf rs rd (Val.neg (rs rd)) m
  | .Pnegq rd => nextSetNf rs rd (Val.negl (rs rd)) m
  | .Paddl_ri rd n => nextSetNf rs rd (Val.add (rs rd) (.Vint n)) m
  | .Paddq_ri rd n => nextSetNf rs rd (Val.addl (rs rd) (.Vlong n)) m
  | .Psubl_rr rd r1 => nextSetNf rs rd (Val.sub (rs rd) (rs r1)) m
  | .Psubq_rr rd r1 => nextSetNf rs rd (Val.subl (rs rd) (rs r1)) m
  | .Pimull_rr rd r1 => nextSetNf rs rd (Val.mul (rs rd) (rs r1)) m
  | .Pimulq_rr rd r1 => nextSetNf rs rd (Val.mull (rs rd) (rs r1)) m
  | .Pimull_ri rd n => nextSetNf rs rd (Val.mul (rs rd) (.Vint n)) m
  | .Pimulq_ri rd n => nextSetNf rs rd (Val.mull (rs rd) (.Vlong n)) m
  | .Pimull_r r1 =>
      .Next (nextinstrNf ((rs.set (.IR .RAX) (Val.mul (rs (.IR .RAX)) (rs r1))).set
        (.IR .RDX) (Val.mulhs (rs (.IR .RAX)) (rs r1)))) m
  | .Pimulq_r r1 =>
      .Next (nextinstrNf ((rs.set (.IR .RAX) (Val.mull (rs (.IR .RAX)) (rs r1))).set
        (.IR .RDX) (Val.mullhs (rs (.IR .RAX)) (rs r1)))) m
  | .Pmull_r r1 =>
      .Next (nextinstrNf ((rs.set (.IR .RAX) (Val.mul (rs (.IR .RAX)) (rs r1))).set
        (.IR .RDX) (Val.mulhu (rs (.IR .RAX)) (rs r1)))) m
  | .Pmulq_r r1 =>
      .Next (nextinstrNf ((rs.set (.IR .RAX) (Val.mull (rs (.IR .RAX)) (rs r1))).set
        (.IR .RDX) (Val.mullhu (rs (.IR .RAX)) (rs r1)))) m
  | .Pcltd => nextSetNf rs (.IR .RDX) (Val.shr (rs (.IR .RAX)) (.Vint (Integers.Int.repr 31))) m
  | .Pcqto => nextSetNf rs (.IR .RDX) (Val.shrl (rs (.IR .RAX)) (.Vint (Integers.Int.repr 63))) m
  | .Pdivl r1 => execDiv projInt .Vint Integers.Int.divmodu2 r1 rs m
  | .Pdivq r1 => execDiv projLong .Vlong Integers.Int64.divmodu2 r1 rs m
  | .Pidivl r1 => execDiv projInt .Vint Integers.Int.divmods2 r1 rs m
  | .Pidivq r1 => execDiv projLong .Vlong Integers.Int64.divmods2 r1 rs m
  | .Pandl_rr rd r1 => nextSetNf rs rd (Val.and (rs rd) (rs r1)) m
  | .Pandq_rr rd r1 => nextSetNf rs rd (Val.andl (rs rd) (rs r1)) m
  | .Pandl_ri rd n => nextSetNf rs rd (Val.and (rs rd) (.Vint n)) m
  | .Pandq_ri rd n => nextSetNf rs rd (Val.andl (rs rd) (.Vlong n)) m
  | .Porl_rr rd r1 => nextSetNf rs rd (Val.or (rs rd) (rs r1)) m
  | .Porq_rr rd r1 => nextSetNf rs rd (Val.orl (rs rd) (rs r1)) m
  | .Porl_ri rd n => nextSetNf rs rd (Val.or (rs rd) (.Vint n)) m
  | .Porq_ri rd n => nextSetNf rs rd (Val.orl (rs rd) (.Vlong n)) m
  | .Pxorl_r rd => nextSetNf rs rd Val.Vzero m
  | .Pxorq_r rd => nextSetNf rs rd (.Vlong Integers.Int64.zero) m
  | .Pxorl_rr rd r1 => nextSetNf rs rd (Val.xor (rs rd) (rs r1)) m
  | .Pxorq_rr rd r1 => nextSetNf rs rd (Val.xorl (rs rd) (rs r1)) m
  | .Pxorl_ri rd n => nextSetNf rs rd (Val.xor (rs rd) (.Vint n)) m
  | .Pxorq_ri rd n => nextSetNf rs rd (Val.xorl (rs rd) (.Vlong n)) m
  | .Pnotl rd => nextSetNf rs rd (Val.notint (rs rd)) m
  | .Pnotq rd => nextSetNf rs rd (Val.notl (rs rd)) m
  | .Psall_rcl rd => nextSetNf rs rd (Val.shl (rs rd) (rs (.IR .RCX))) m
  | .Psalq_rcl rd => nextSetNf rs rd (Val.shll (rs rd) (rs (.IR .RCX))) m
  | .Psall_ri rd n => nextSetNf rs rd (Val.shl (rs rd) (.Vint n)) m
  | .Psalq_ri rd n => nextSetNf rs rd (Val.shll (rs rd) (.Vint n)) m
  | .Pshrl_rcl rd => nextSetNf rs rd (Val.shru (rs rd) (rs (.IR .RCX))) m
  | .Pshrq_rcl rd => nextSetNf rs rd (Val.shrlu (rs rd) (rs (.IR .RCX))) m
  | .Pshrl_ri rd n => nextSetNf rs rd (Val.shru (rs rd) (.Vint n)) m
  | .Pshrq_ri rd n => nextSetNf rs rd (Val.shrlu (rs rd) (.Vint n)) m
  | .Psarl_rcl rd => nextSetNf rs rd (Val.shr (rs rd) (rs (.IR .RCX))) m
  | .Psarq_rcl rd => nextSetNf rs rd (Val.shrl (rs rd) (rs (.IR .RCX))) m
  | .Psarl_ri rd n => nextSetNf rs rd (Val.shr (rs rd) (.Vint n)) m
  | .Psarq_ri rd n => nextSetNf rs rd (Val.shrl (rs rd) (.Vint n)) m
  | .Pshld_ri rd r1 n =>
      nextSetNf rs rd (Val.or (Val.shl (rs rd) (.Vint n))
        (Val.shru (rs r1) (.Vint (Integers.Int.sub Integers.Int.iwordsize n)))) m
  | .Prorl_ri rd n => nextSetNf rs rd (Val.ror (rs rd) (.Vint n)) m
  | .Prorq_ri rd n => nextSetNf rs rd (Val.rorl (rs rd) (.Vint n)) m
  | .Pcmpl_rr r1 r2 => .Next (nextinstr (compareInts (rs r1) (rs r2) rs m)) m
  | .Pcmpq_rr r1 r2 => .Next (nextinstr (compareLongs (rs r1) (rs r2) rs m)) m
  | .Pcmpl_ri r1 n => .Next (nextinstr (compareInts (rs r1) (.Vint n) rs m)) m
  | .Pcmpq_ri r1 n => .Next (nextinstr (compareLongs (rs r1) (.Vlong n) rs m)) m
  | .Ptestl_rr r1 r2 =>
      .Next (nextinstr (compareInts (Val.and (rs r1) (rs r2)) Val.Vzero rs m)) m
  | .Ptestq_rr r1 r2 =>
      .Next (nextinstr (compareLongs (Val.andl (rs r1) (rs r2))
        (.Vlong Integers.Int64.zero) rs m)) m
  | .Ptestl_ri r1 n =>
      .Next (nextinstr (compareInts (Val.and (rs r1) (.Vint n)) Val.Vzero rs m)) m
  | .Ptestq_ri r1 n =>
      .Next (nextinstr (compareLongs (Val.andl (rs r1) (.Vlong n))
        (.Vlong Integers.Int64.zero) rs m)) m
  | .Pcmov c rd r1 =>
      let v := match evalTestcond c rs with
        | some b => if b then rs r1 else rs rd
        | none => .Vundef
      nextSet rs rd v m
  | .Psetcc c rd => nextSet rs rd (Val.ofOptbool (evalTestcond c rs)) m
  -- Double-precision floating-point arithmetic
  | .Paddd_ff rd r1 => nextSet rs rd (Val.addf (rs rd) (rs r1)) m
  | .Psubd_ff rd r1 => nextSet rs rd (Val.subf (rs rd) (rs r1)) m
  | .Pmuld_ff rd r1 => nextSet rs rd (Val.mulf (rs rd) (rs r1)) m
  | .Pdivd_ff rd r1 => nextSet rs rd (Val.divf (rs rd) (rs r1)) m
  | .Pnegd rd => nextSet rs rd (Val.negf (rs rd)) m
  | .Pabsd rd => nextSet rs rd (Val.absf (rs rd)) m
  | .Pcomisd_ff r1 r2 => .Next (nextinstr (compareFloats (rs r1) (rs r2) rs)) m
  | .Pxorpd_f rd => nextSetNf rs rd (.Vfloat Floats.Float.zero) m
  | .Pmaxsd rd r1 => nextSet rs rd (Op.maxf (rs rd) (rs r1)) m
  | .Pminsd rd r1 => nextSet rs rd (Op.minf (rs rd) (rs r1)) m
  -- Single-precision floating-point arithmetic
  | .Padds_ff rd r1 => nextSet rs rd (Val.addfs (rs rd) (rs r1)) m
  | .Psubs_ff rd r1 => nextSet rs rd (Val.subfs (rs rd) (rs r1)) m
  | .Pmuls_ff rd r1 => nextSet rs rd (Val.mulfs (rs rd) (rs r1)) m
  | .Pdivs_ff rd r1 => nextSet rs rd (Val.divfs (rs rd) (rs r1)) m
  | .Pnegs rd => nextSet rs rd (Val.negfs (rs rd)) m
  | .Pabss rd => nextSet rs rd (Val.absfs (rs rd)) m
  | .Pcomiss_ff r1 r2 => .Next (nextinstr (compareFloats32 (rs r1) (rs r2) rs)) m
  | .Pxorps_f rd => nextSetNf rs rd (.Vsingle Floats.Float32.zero) m
  -- Branches and calls
  | .Pjmp_l lbl => gotoLabel f lbl rs m
  | .Pjmp_s id _ => .Next (rs.set .PC (Genv.symbolAddress ge id Integers.Ptrofs.zero)) m
  | .Pjmp_r r _ => .Next (rs.set .PC (rs r)) m
  | .Pjcc cond lbl =>
      match evalTestcond cond rs with
      | some true => gotoLabel f lbl rs m
      | some false => .Next (nextinstr rs) m
      | none => .Stuck
  | .Pjcc2 cond1 cond2 lbl =>
      match evalTestcond cond1 rs, evalTestcond cond2 rs with
      | some true, some true => gotoLabel f lbl rs m
      | some _, some _ => .Next (nextinstr rs) m
      | _, _ => .Stuck
  | .Pjmptbl r tbl =>
      match rs r with
      | .Vint n =>
          match CminorSel.listNthZ tbl (Integers.Int.unsigned n) with
          | none => .Stuck
          | some lbl =>
              gotoLabel f lbl ((rs.set (.IR .RAX) .Vundef).set (.IR .RDX) .Vundef) m
      | _ => .Stuck
  | .Pcall_s id _ =>
      .Next ((rs.set .RA (Val.offsetPtr (rs .PC) Integers.Ptrofs.one)).set .PC
        (Genv.symbolAddress ge id Integers.Ptrofs.zero)) m
  | .Pcall_r r _ =>
      .Next ((rs.set .RA (Val.offsetPtr (rs .PC) Integers.Ptrofs.one)).set .PC (rs r)) m
  | .Pret => .Next (rs.set .PC (rs .RA)) m
  -- Saving and restoring registers
  | .Pmov_rm_a rd a => load (if Archi.ptr64 then .Many64 else .Many32) m a rs rd
  | .Pmov_mr_a a r1 => store (if Archi.ptr64 then .Many64 else .Many32) m a rs r1 []
  | .Pmovsd_fm_a rd a => load .Many64 m a rs rd
  | .Pmovsd_mf_a a r1 => store .Many64 m a rs r1 []
  -- Pseudo-instructions
  | .Plabel _ => .Next (nextinstr rs) m
  | .Pallocframe sz ofs_ra ofs_link =>
      let (m1, stk) := Mem.alloc m 0 sz
      let sp : Val := .Vptr stk Integers.Ptrofs.zero
      match Mem.storev Mptr m1 (Val.offsetPtr sp ofs_link) (rs (.IR .RSP)) with
      | none => .Stuck
      | some m2 =>
          match Mem.storev Mptr m2 (Val.offsetPtr sp ofs_ra) (rs .RA) with
          | none => .Stuck
          | some m3 =>
              .Next (nextinstr ((rs.set (.IR .RAX) (rs (.IR .RSP))).set (.IR .RSP) sp)) m3
  | .Pfreeframe sz ofs_ra ofs_link =>
      match Mem.loadv Mptr m (Val.offsetPtr (rs (.IR .RSP)) ofs_ra) with
      | none => .Stuck
      | some ra =>
          match Mem.loadv Mptr m (Val.offsetPtr (rs (.IR .RSP)) ofs_link) with
          | none => .Stuck
          | some sp =>
              match rs (.IR .RSP) with
              | .Vptr stk _ =>
                  match Mem.free m stk 0 sz with
                  | none => .Stuck
                  | some m' => .Next (nextinstr ((rs.set (.IR .RSP) sp).set .RA ra)) m'
              | _ => .Stuck
  | .Pbuiltin .. => .Stuck
  -- Not generated by `Asmgen`, not modeled
  | .Padcl_ri .. | .Padcl_rr .. | .Paddl_mi .. | .Paddl_rr .. | .Pbsfl .. | .Pbsfq ..
  | .Pbsrl .. | .Pbsrq .. | .Pbswap64 .. | .Pbswap32 .. | .Pbswap16 .. | .Pcfi_adjust ..
  | .Pfmadd132 .. | .Pfmadd213 .. | .Pfmadd231 .. | .Pfmsub132 .. | .Pfmsub213 ..
  | .Pfmsub231 .. | .Pfnmadd132 .. | .Pfnmadd213 .. | .Pfnmadd231 .. | .Pfnmsub132 ..
  | .Pfnmsub213 .. | .Pfnmsub231 .. | .Pmovb_rm .. | .Pmovq_rf .. | .Pmovsq_rm ..
  | .Pmovsq_mr .. | .Pmovsb | .Pmovsw | .Pmovw_rm .. | .Pnop | .Prep_movsl | .Psbbl_rr ..
  | .Psqrtsd .. | .Psubl_ri .. | .Psubq_ri .. => .Stuck

end RELSEM

/-- `Asm.preg_of`: the Asm view of a machine register. -/
def pregOf (r : Mreg) : Preg :=
  match r with
  | .AX => .IR .RAX | .BX => .IR .RBX | .CX => .IR .RCX | .DX => .IR .RDX
  | .SI => .IR .RSI | .DI => .IR .RDI | .BP => .IR .RBP
  | .R8 => .IR .R8 | .R9 => .IR .R9 | .R10 => .IR .R10 | .R11 => .IR .R11
  | .R12 => .IR .R12 | .R13 => .IR .R13 | .R14 => .IR .R14 | .R15 => .IR .R15
  | .X0 => .FR .XMM0 | .X1 => .FR .XMM1 | .X2 => .FR .XMM2 | .X3 => .FR .XMM3
  | .X4 => .FR .XMM4 | .X5 => .FR .XMM5 | .X6 => .FR .XMM6 | .X7 => .FR .XMM7
  | .X8 => .FR .XMM8 | .X9 => .FR .XMM9 | .X10 => .FR .XMM10 | .X11 => .FR .XMM11
  | .X12 => .FR .XMM12 | .X13 => .FR .XMM13 | .X14 => .FR .XMM14 | .X15 => .FR .XMM15
  | .FP0 => .ST0

/-- `Asm.undef_caller_save_regs`: undefine all registers except `SP` and the
callee-save registers. -/
def undefCallerSaveRegs (win64 : Bool) (rs : Regset) : Regset := fun r =>
  if decide (r = .IR SP) ||
     decide (r ∈ ((Mreg.allMregs.filter (isCalleeSave win64)).map pregOf)) then rs r
  else .Vundef

/-- `Asm.extcall_arg` -/
inductive ExtcallArg (win64 : Bool) (rs : Regset) (m : Mem) : Loc → Val → Prop where
  | reg (r) : ExtcallArg win64 rs m (.R r) (rs (pregOf r))
  | stack (ofs ty bofs v) :
      bofs = Stacklayout.feOfsArg win64 + 4 * ofs →
      Mem.loadv (Chunk.ofTyp ty) m
        (Val.offsetPtr (rs (.IR .RSP)) (Integers.Ptrofs.repr bofs)) = some v →
      ExtcallArg win64 rs m (.S .Outgoing ofs ty) v

/-- `Asm.extcall_arg_pair` -/
inductive ExtcallArgPair (win64 : Bool) (rs : Regset) (m : Mem) : RPair Loc → Val → Prop where
  | one (l v) : ExtcallArg win64 rs m l v → ExtcallArgPair win64 rs m (.One l) v
  | twolong (hi lo vhi vlo) :
      ExtcallArg win64 rs m hi vhi → ExtcallArg win64 rs m lo vlo →
      ExtcallArgPair win64 rs m (.Twolong hi lo) (Val.longofwords vhi vlo)

/-- `Asm.extcall_arguments` -/
def ExtcallArguments (win64 : Bool) (rs : Regset) (m : Mem) (sg : Signature)
    (args : List Val) : Prop :=
  ListForall2 (ExtcallArgPair win64 rs m) (locArguments win64 sg) args

/-- `Asm.loc_external_result` -/
def locExternalResult (sg : Signature) : RPair Preg := RPair.map pregOf (locResult sg)

/-- `Asm.state` -/
inductive State where
  | State (rs : Regset) (m : Mem)

section RELSEM
variable (win64 : Bool) (ge : CGenv)

/-- `Asm.step` -/
inductive Step : State → Trace → State → Prop where
  | exec_step_internal (b ofs f i rs m rs' m') :
      rs .PC = .Vptr b ofs →
      Genv.findFunctPtr ge b = some (.Internal f) →
      findInstr (Integers.Ptrofs.unsigned ofs) f.fn_code = some i →
      execInstr ge f i rs m = .Next rs' m' →
      Step (.State rs m) E0 (.State rs' m')
  | exec_step_builtin (b ofs f ef args res rs m vargs t vres rs' m') :
      rs .PC = .Vptr b ofs →
      Genv.findFunctPtr ge b = some (.Internal f) →
      findInstr (Integers.Ptrofs.unsigned ofs) f.fn_code = some (.Pbuiltin ef args res) →
      EvalBuiltinArgs ge.toSenv rs (rs (.IR .RSP)) m args vargs →
      externalCall ef ge.toSenv vargs m t vres m' →
      rs' = nextinstrNf (setRes res vres
        (undefRegs ((destroyedByBuiltin ef).map pregOf) rs)) →
      Step (.State rs m) t (.State rs' m')
  | exec_step_external (b ef args res rs m t rs' m') :
      rs .PC = .Vptr b Integers.Ptrofs.zero →
      Genv.findFunctPtr ge b = some (.External ef) →
      ExtcallArguments win64 rs m ef.sig args →
      externalCall ef ge.toSenv args m t res m' →
      rs' = (setPair (locExternalResult ef.sig) res (undefCallerSaveRegs win64 rs)).set
        .PC (rs .RA) →
      Step (.State rs m) t (.State rs' m')

end RELSEM

/-- `Asm.initial_state` -/
inductive InitialState (p : Program) : State → Prop where
  | intro (m0) :
      p.initMem = some m0 →
      InitialState p (.State
        (((Regset.init .Vundef).set .PC
          (Genv.symbolAddress p.globalenv p.prog_main Integers.Ptrofs.zero)).set
          .RA Val.Vnullptr |>.set (.IR .RSP) Val.Vnullptr) m0)

/-- `Asm.final_state` -/
inductive FinalState : State → Integers.Int → Prop where
  | intro (rs m r) :
      rs .PC = Val.Vnullptr →
      rs (.IR .RAX) = .Vint r →
      FinalState (.State rs m) r

/-- `Asm.semantics` -/
def semantics (win64 : Bool) (p : Program) : Semantics where
  state := State
  step := Step win64 p.globalenv
  initial_state := InitialState p
  final_state := FinalState
  symbolenv := Genv.toSenv p.globalenv

theorem extcallArg_determ {win64 rs m l v1 v2} (h1 : ExtcallArg win64 rs m l v1)
    (h2 : ExtcallArg win64 rs m l v2) : v1 = v2 := by
  cases h1 with
  | reg => cases h2; rfl
  | stack _ _ _ _ he h => cases h2 with
    | stack _ _ _ _ he' h' => subst he he'; rw [h] at h'; cases h'; rfl

theorem extcallArgPair_determ {win64 rs m p v1 v2} (h1 : ExtcallArgPair win64 rs m p v1)
    (h2 : ExtcallArgPair win64 rs m p v2) : v1 = v2 := by
  cases h1 with
  | one _ _ h => cases h2 with
    | one _ _ h' => exact extcallArg_determ h h'
  | twolong _ _ _ _ ha hb => cases h2 with
    | twolong _ _ _ _ ha' hb' => rw [extcallArg_determ ha ha', extcallArg_determ hb hb']

/-- `Asm.extcall_arguments_determ` -/
theorem extcallArguments_determ {win64 rs m sg args1 args2}
    (h1 : ExtcallArguments win64 rs m sg args1) (h2 : ExtcallArguments win64 rs m sg args2) :
    args1 = args2 := by
  unfold ExtcallArguments at h1 h2
  generalize locArguments win64 sg = l at h1 h2
  induction h1 generalizing args2 with
  | nil => cases h2; rfl
  | cons ha _ ih => cases h2 with
    | cons hb hl => rw [extcallArgPair_determ ha hb, ih hl]

/-- `Asm.data_preg` -/
def dataPreg (r : Preg) : Bool :=
  match r with
  | .PC => false
  | .IR _ => true
  | .FR _ => true
  | .ST0 => true
  | .CR _ => false
  | .RA => false

end Asm
end X86
end CC
