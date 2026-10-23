/-
  Translation from Mach to x86 assembly — port of `x86/Asmgen.v`
  (whole file).

  Ported: `ireg_of`, `freg_of`, `mk_mov`, `mk_shrximm`, `mk_shrxlimm`,
  `low_ireg`, `mk_intconv`, `addressing_mentions`, `mk_storebyte`,
  `loadind`, `storeind`, `transl_addressing`, `normalize_addrmode_32/64`,
  `floatcomp`, `floatcomp32`, `transl_cond`,
  `testcond_for_signed/unsigned_comparison`, `extcond`,
  `testcond_for_condition`, `mk_setcc_base`, `mk_setcc`, `mk_jcc`,
  `negate_testcond`, `mk_sel`, `transl_sel`, `transl_op`, `transl_load`,
  `transl_store`, `transl_instr`, `it1_is_parent`, `transl_code`,
  `transl_code_rec`, `transl_code'`, `transl_function`, `transf_function`,
  `transf_fundef`, `transf_program`.
  Also proved: `transl_code'_transl_code` (from `Asmgenproof.v`).

  Differences from Rocq: `assertion b; k` is `assert b k`; error messages
  are plain strings.
-/
import CCLib.x86.Asm
import CCLib.x86.Mach

namespace CC
namespace X86
namespace Asmgen

open Asm Op

/-- `assertion b; k` of Rocq's error monad. -/
def assert {A : Type} (b : Bool) (k : Res A) : Res A :=
  if b then k else .Error "Assertion failed"

/-! ## Extracting integer or float registers -/

/-- `Asmgen.ireg_of` -/
def iregOf (r : Mreg) : Res Ireg :=
  match pregOf r with
  | .IR mr => .OK mr
  | _ => .Error "Asmgen.ireg_of"

/-- `Asmgen.freg_of` -/
def fregOf (r : Mreg) : Res Freg :=
  match pregOf r with
  | .FR mr => .OK mr
  | _ => .Error "Asmgen.freg_of"

/-! ## Smart constructors -/

/-- `Asmgen.mk_mov` -/
def mkMov (rd rs : Preg) (k : Code) : Res Code :=
  match rd, rs with
  | .IR rd, .IR rs => .OK (.Pmov_rr rd rs :: k)
  | .FR rd, .FR rs => .OK (.Pmovsd_ff rd rs :: k)
  | _, _ => .Error "Asmgen.mk_mov"

/-- `Asmgen.mk_shrximm` -/
def mkShrximm (n : Integers.Int) (k : Code) : Res Code :=
  let p := Integers.Int.sub (Integers.Int.shl Integers.Int.one n) Integers.Int.one
  .OK (.Ptestl_rr .RAX .RAX ::
       .Pleal .RCX (.Addrmode (some .RAX) none (.inl (Integers.Int.unsigned p))) ::
       .Pcmov .Cond_l .RAX .RCX ::
       .Psarl_ri .RAX n :: k)

/-- `Asmgen.mk_shrxlimm` -/
def mkShrxlimm (n : Integers.Int) (k : Code) : Res Code :=
  .OK (if Integers.Int.eq n Integers.Int.zero then .Pmov_rr .RAX .RAX :: k else
       .Pcqto ::
       .Pshrq_ri .RDX (Integers.Int.sub (Integers.Int.repr 64) n) ::
       .Pleaq .RAX (.Addrmode (some .RAX) (some (.RDX, 1)) (.inl 0)) ::
       .Psarq_ri .RAX n :: k)

/-- `Asmgen.low_ireg` -/
def lowIreg : Ireg → Bool
  | .RAX | .RBX | .RCX | .RDX => true
  | _ => false

/-- `Asmgen.mk_intconv` -/
def mkIntconv (mk : Ireg → Ireg → Instruction) (rd rs : Ireg) (k : Code) : Res Code :=
  if Archi.ptr64 || lowIreg rs then .OK (mk rd rs :: k)
  else .OK (.Pmov_rr .RAX rs :: mk rd .RAX :: k)

/-- `Asmgen.addressing_mentions` -/
def addressingMentions (addr : Addrmode) (r : Ireg) : Bool :=
  match addr with
  | .Addrmode base displ _ =>
      (match base with | some r' => decide (r = r') | none => false) ||
      (match displ with | some (r', _) => decide (r = r') | none => false)

/-- `Asmgen.mk_storebyte` -/
def mkStorebyte (addr : Addrmode) (rs : Ireg) (k : Code) : Res Code :=
  if Archi.ptr64 || lowIreg rs then .OK (.Pmovb_mr addr rs :: k)
  else if addressingMentions addr .RAX then
    .OK (.Pleal .RCX addr :: .Pmov_rr .RAX rs ::
         .Pmovb_mr (.Addrmode (some .RCX) none (.inl 0)) .RAX :: k)
  else .OK (.Pmov_rr .RAX rs :: .Pmovb_mr addr .RAX :: k)

/-! ## Accessing slots in the stack frame -/

/-- `Asmgen.loadind` -/
def loadind (base : Ireg) (ofs : Integers.Ptrofs) (ty : ATyp) (dst : Mreg) (k : Code) :
    Res Code :=
  let a : Addrmode := .Addrmode (some base) none (.inl (Integers.Ptrofs.unsigned ofs))
  match ty, pregOf dst with
  | .Tint, .IR r => .OK (.Pmovl_rm r a :: k)
  | .Tlong, .IR r => .OK (.Pmovq_rm r a :: k)
  | .Tsingle, .FR r => .OK (.Pmovss_fm r a :: k)
  | .Tsingle, .ST0 => .OK (.Pflds_m a :: k)
  | .Tfloat, .FR r => .OK (.Pmovsd_fm r a :: k)
  | .Tfloat, .ST0 => .OK (.Pfldl_m a :: k)
  | .Tany32, .IR r =>
      if Archi.ptr64 then .Error "Asmgen.loadind1" else .OK (.Pmov_rm_a r a :: k)
  | .Tany64, .IR r =>
      if Archi.ptr64 then .OK (.Pmov_rm_a r a :: k) else .Error "Asmgen.loadind2"
  | .Tany64, .FR r => .OK (.Pmovsd_fm_a r a :: k)
  | _, _ => .Error "Asmgen.loadind"

/-- `Asmgen.storeind` -/
def storeind (src : Mreg) (base : Ireg) (ofs : Integers.Ptrofs) (ty : ATyp) (k : Code) :
    Res Code :=
  let a : Addrmode := .Addrmode (some base) none (.inl (Integers.Ptrofs.unsigned ofs))
  match ty, pregOf src with
  | .Tint, .IR r => .OK (.Pmovl_mr a r :: k)
  | .Tlong, .IR r => .OK (.Pmovq_mr a r :: k)
  | .Tsingle, .FR r => .OK (.Pmovss_mf a r :: k)
  | .Tsingle, .ST0 => .OK (.Pfstps_m a :: k)
  | .Tfloat, .FR r => .OK (.Pmovsd_mf a r :: k)
  | .Tfloat, .ST0 => .OK (.Pfstpl_m a :: k)
  | .Tany32, .IR r =>
      if Archi.ptr64 then .Error "Asmgen.storeind1" else .OK (.Pmov_mr_a a r :: k)
  | .Tany64, .IR r =>
      if Archi.ptr64 then .OK (.Pmov_mr_a a r :: k) else .Error "Asmgen.storeind2"
  | .Tany64, .FR r => .OK (.Pmovsd_mf_a a r :: k)
  | _, _ => .Error "Asmgen.storeind"

/-! ## Addressing modes -/

/-- `Asmgen.transl_addressing` -/
def translAddressing (a : Addressing) (args : List Mreg) : Res Addrmode :=
  match a, args with
  | .Aindexed n, [a1] => do
      let r1 ← iregOf a1; pure (.Addrmode (some r1) none (.inl n))
  | .Aindexed2 n, [a1, a2] => do
      let r1 ← iregOf a1; let r2 ← iregOf a2
      pure (.Addrmode (some r1) (some (r2, 1)) (.inl n))
  | .Ascaled sc n, [a1] => do
      let r1 ← iregOf a1; pure (.Addrmode none (some (r1, sc)) (.inl n))
  | .Aindexed2scaled sc n, [a1, a2] => do
      let r1 ← iregOf a1; let r2 ← iregOf a2
      pure (.Addrmode (some r1) (some (r2, sc)) (.inl n))
  | .Aglobal id ofs, [] => .OK (.Addrmode none none (.inr (id, ofs)))
  | .Abased id ofs, [a1] => do
      let r1 ← iregOf a1; pure (.Addrmode (some r1) none (.inr (id, ofs)))
  | .Abasedscaled sc id ofs, [a1] => do
      let r1 ← iregOf a1; pure (.Addrmode none (some (r1, sc)) (.inr (id, ofs)))
  | .Ainstack n, [] => .OK (.Addrmode (some .RSP) none (.inl (Integers.Ptrofs.signed n)))
  | _, _ => .Error "Asmgen.transl_addressing"

/-- `Asmgen.normalize_addrmode_32` -/
def normalizeAddrmode32 (a : Addrmode) : Addrmode :=
  match a with
  | .Addrmode base ofs (.inl n) =>
      .Addrmode base ofs (.inl (Integers.Int.signed (Integers.Int.repr n)))
  | .Addrmode _ _ (.inr _) => a

/-- `Asmgen.normalize_addrmode_64`: displacements that do not fit in 32 bits
are split off into a separate 64-bit addition. -/
def normalizeAddrmode64 (a : Addrmode) : Addrmode × Option Integers.Int64 :=
  match a with
  | .Addrmode base ofs (.inl n) =>
      if Op.offsetInRange n then (a, none)
      else (.Addrmode base ofs (.inl 0), some (Integers.Int64.repr n))
  | .Addrmode base ofs (.inr (id, delta)) =>
      if Op.ptroffsetInRange delta || !Archi.ptr64 then (a, none)
      else (.Addrmode base ofs (.inr (id, Integers.Ptrofs.zero)),
            some (Integers.Ptrofs.to_int64 delta))

/-! ## Conditions -/

/-- `Asmgen.floatcomp` -/
def floatcomp (cmp : Comparison) (r1 r2 : Freg) : Instruction :=
  match cmp with
  | .Clt | .Cle => .Pcomisd_ff r2 r1
  | .Ceq | .Cne | .Cgt | .Cge => .Pcomisd_ff r1 r2

/-- `Asmgen.floatcomp32` -/
def floatcomp32 (cmp : Comparison) (r1 r2 : Freg) : Instruction :=
  match cmp with
  | .Clt | .Cle => .Pcomiss_ff r2 r1
  | .Ceq | .Cne | .Cgt | .Cge => .Pcomiss_ff r1 r2

/-- `Asmgen.transl_cond` -/
def translCond (cond : Condition) (args : List Mreg) (k : Code) : Res Code :=
  match cond, args with
  | .Ccomp _, [a1, a2] => do
      let r1 ← iregOf a1; let r2 ← iregOf a2; pure (.Pcmpl_rr r1 r2 :: k)
  | .Ccompu _, [a1, a2] => do
      let r1 ← iregOf a1; let r2 ← iregOf a2; pure (.Pcmpl_rr r1 r2 :: k)
  | .Ccompimm _ n, [a1] => do
      let r1 ← iregOf a1
      pure (if n = Integers.Int.zero then .Ptestl_rr r1 r1 :: k else .Pcmpl_ri r1 n :: k)
  | .Ccompuimm _ n, [a1] => do
      let r1 ← iregOf a1; pure (.Pcmpl_ri r1 n :: k)
  | .Ccompl _, [a1, a2] => do
      let r1 ← iregOf a1; let r2 ← iregOf a2; pure (.Pcmpq_rr r1 r2 :: k)
  | .Ccomplu _, [a1, a2] => do
      let r1 ← iregOf a1; let r2 ← iregOf a2; pure (.Pcmpq_rr r1 r2 :: k)
  | .Ccomplimm _ n, [a1] => do
      let r1 ← iregOf a1
      pure (if n = Integers.Int64.zero then .Ptestq_rr r1 r1 :: k else .Pcmpq_ri r1 n :: k)
  | .Ccompluimm _ n, [a1] => do
      let r1 ← iregOf a1; pure (.Pcmpq_ri r1 n :: k)
  | .Ccompf cmp, [a1, a2] => do
      let r1 ← fregOf a1; let r2 ← fregOf a2; pure (floatcomp cmp r1 r2 :: k)
  | .Cnotcompf cmp, [a1, a2] => do
      let r1 ← fregOf a1; let r2 ← fregOf a2; pure (floatcomp cmp r1 r2 :: k)
  | .Ccompfs cmp, [a1, a2] => do
      let r1 ← fregOf a1; let r2 ← fregOf a2; pure (floatcomp32 cmp r1 r2 :: k)
  | .Cnotcompfs cmp, [a1, a2] => do
      let r1 ← fregOf a1; let r2 ← fregOf a2; pure (floatcomp32 cmp r1 r2 :: k)
  | .Cmaskzero n, [a1] => do
      let r1 ← iregOf a1; pure (.Ptestl_ri r1 n :: k)
  | .Cmasknotzero n, [a1] => do
      let r1 ← iregOf a1; pure (.Ptestl_ri r1 n :: k)
  | _, _ => .Error "Asmgen.transl_cond"

/-- `Asmgen.testcond_for_signed_comparison` -/
def testcondForSignedComparison : Comparison → Testcond
  | .Ceq => .Cond_e | .Cne => .Cond_ne | .Clt => .Cond_l
  | .Cle => .Cond_le | .Cgt => .Cond_g | .Cge => .Cond_ge

/-- `Asmgen.testcond_for_unsigned_comparison` -/
def testcondForUnsignedComparison : Comparison → Testcond
  | .Ceq => .Cond_e | .Cne => .Cond_ne | .Clt => .Cond_b
  | .Cle => .Cond_be | .Cgt => .Cond_a | .Cge => .Cond_ae

/-- `Asmgen.extcond`: a processor condition, or the conjunction or
disjunction of two (needed for floating-point equality). -/
inductive Extcond where
  | Cond_base (c : Testcond)
  | Cond_or (c1 c2 : Testcond)
  | Cond_and (c1 c2 : Testcond)

/-- `Asmgen.testcond_for_condition` -/
def testcondForCondition (cond : Condition) : Extcond :=
  match cond with
  | .Ccomp c | .Ccompimm c _ | .Ccompl c | .Ccomplimm c _ =>
      .Cond_base (testcondForSignedComparison c)
  | .Ccompu c | .Ccompuimm c _ | .Ccomplu c | .Ccompluimm c _ =>
      .Cond_base (testcondForUnsignedComparison c)
  | .Ccompf c | .Ccompfs c =>
      match c with
      | .Ceq => .Cond_and .Cond_np .Cond_e
      | .Cne => .Cond_or .Cond_p .Cond_ne
      | .Clt => .Cond_base .Cond_a
      | .Cle => .Cond_base .Cond_ae
      | .Cgt => .Cond_base .Cond_a
      | .Cge => .Cond_base .Cond_ae
  | .Cnotcompf c | .Cnotcompfs c =>
      match c with
      | .Ceq => .Cond_or .Cond_p .Cond_ne
      | .Cne => .Cond_and .Cond_np .Cond_e
      | .Clt => .Cond_base .Cond_be
      | .Cle => .Cond_base .Cond_b
      | .Cgt => .Cond_base .Cond_be
      | .Cge => .Cond_base .Cond_b
  | .Cmaskzero _ => .Cond_base .Cond_e
  | .Cmasknotzero _ => .Cond_base .Cond_ne

/-- `Asmgen.mk_setcc_base` -/
def mkSetccBase (cond : Extcond) (rd : Ireg) (k : Code) : Code :=
  match cond with
  | .Cond_base c => .Psetcc c rd :: k
  | .Cond_and c1 c2 =>
      if rd = .RAX then .Psetcc c1 .RAX :: .Psetcc c2 .RCX :: .Pandl_rr .RAX .RCX :: k
      else .Psetcc c1 .RAX :: .Psetcc c2 rd :: .Pandl_rr rd .RAX :: k
  | .Cond_or c1 c2 =>
      if rd = .RAX then .Psetcc c1 .RAX :: .Psetcc c2 .RCX :: .Porl_rr .RAX .RCX :: k
      else .Psetcc c1 .RAX :: .Psetcc c2 rd :: .Porl_rr rd .RAX :: k

/-- `Asmgen.mk_setcc` -/
def mkSetcc (cond : Extcond) (rd : Ireg) (k : Code) : Code :=
  if Archi.ptr64 || lowIreg rd then mkSetccBase cond rd k
  else mkSetccBase cond .RAX (.Pmov_rr rd .RAX :: k)

/-- `Asmgen.mk_jcc` -/
def mkJcc (cond : Extcond) (lbl : Label) (k : Code) : Code :=
  match cond with
  | .Cond_base c => .Pjcc c lbl :: k
  | .Cond_and c1 c2 => .Pjcc2 c1 c2 lbl :: k
  | .Cond_or c1 c2 => .Pjcc c1 lbl :: .Pjcc c2 lbl :: k

/-- `Asmgen.negate_testcond` -/
def negateTestcond : Testcond → Testcond
  | .Cond_e => .Cond_ne | .Cond_ne => .Cond_e
  | .Cond_b => .Cond_ae | .Cond_be => .Cond_a
  | .Cond_ae => .Cond_b | .Cond_a => .Cond_be
  | .Cond_l => .Cond_ge | .Cond_le => .Cond_g
  | .Cond_ge => .Cond_l | .Cond_g => .Cond_le
  | .Cond_p => .Cond_np | .Cond_np => .Cond_p

/-- `Asmgen.mk_sel` -/
def mkSel (cond : Extcond) (rd r2 : Ireg) (k : Code) : Res Code :=
  match cond with
  | .Cond_base c => .OK (.Pcmov (negateTestcond c) rd r2 :: k)
  | .Cond_and c1 c2 =>
      .OK (.Pcmov (negateTestcond c1) rd r2 :: .Pcmov (negateTestcond c2) rd r2 :: k)
  | .Cond_or _ _ => .Error "Asmgen.mk_sel"

/-- `Asmgen.transl_sel` -/
def translSel (cond : Condition) (args : List Mreg) (rd r2 : Ireg) (k : Code) : Res Code :=
  if rd = r2 then .OK (.Pmov_rr rd r2 :: k)
  else do
    let k1 ← mkSel (testcondForCondition cond) rd r2 k
    translCond cond args k1

/-! ## Operations -/

/-- A two-address operation on integer registers: `res` must equal `a1`. -/
def iop1 (a1 res : Mreg) (mk : Ireg → Instruction) (k : Code) : Res Code :=
  assert (decide (a1 = res)) (do let r ← iregOf res; pure (mk r :: k))
/-- A two-address binary operation on integer registers. -/
def iop2 (a1 a2 res : Mreg) (mk : Ireg → Ireg → Instruction) (k : Code) : Res Code :=
  assert (decide (a1 = res)) (do let r ← iregOf res; let r2 ← iregOf a2; pure (mk r r2 :: k))
/-- A two-address shift by `CL`. -/
def ishift (a1 a2 res : Mreg) (mk : Ireg → Instruction) (k : Code) : Res Code :=
  assert (decide (a1 = res)) (assert (decide (a2 = .CX))
    (do let r ← iregOf res; pure (mk r :: k)))
/-- A two-address operation on float registers. -/
def fop1 (a1 res : Mreg) (mk : Freg → Instruction) (k : Code) : Res Code :=
  assert (decide (a1 = res)) (do let r ← fregOf res; pure (mk r :: k))
/-- A two-address binary operation on float registers. -/
def fop2 (a1 a2 res : Mreg) (mk : Freg → Freg → Instruction) (k : Code) : Res Code :=
  assert (decide (a1 = res)) (do let r ← fregOf res; let r2 ← fregOf a2; pure (mk r r2 :: k))
/-- High part of a multiplication: `a1 = AX`, result in `DX`. -/
def mulh (a1 a2 res : Mreg) (mk : Ireg → Instruction) (k : Code) : Res Code :=
  assert (decide (a1 = .AX)) (assert (decide (res = .DX))
    (do let r2 ← iregOf a2; pure (mk r2 :: k)))
/-- Division / modulus: `a1 = AX`, `a2 = CX`, result in `dst`. -/
def divop (a1 a2 res dst : Mreg) (c : Code) : Res Code :=
  assert (decide (a1 = .AX)) (assert (decide (a2 = .CX)) (assert (decide (res = dst)) (.OK c)))

/-- `Asmgen.transl_op` -/
def translOp (op : Operation) (args : List Mreg) (res : Mreg) (k : Code) : Res Code :=
  match op, args with
  | .Omove, [a1] => mkMov (pregOf res) (pregOf a1) k
  | .Ointconst n, [] => do
      let r ← iregOf res
      pure ((if n = Integers.Int.zero then .Pxorl_r r else .Pmovl_ri r n) :: k)
  | .Olongconst n, [] => do
      let r ← iregOf res
      pure ((if n = Integers.Int64.zero then .Pxorq_r r else .Pmovq_ri r n) :: k)
  | .Ofloatconst f, [] => do
      let r ← fregOf res
      pure ((if f = Floats.Float.zero then .Pxorpd_f r else .Pmovsd_fi r f) :: k)
  | .Osingleconst f, [] => do
      let r ← fregOf res
      pure ((if f = Floats.Float32.zero then .Pxorps_f r else .Pmovss_fi r f) :: k)
  | .Oindirectsymbol id, [] => do
      let r ← iregOf res; pure (.Pmov_rs r id :: k)
  | .Ocast8signed, [a1] => do
      let r1 ← iregOf a1; let r ← iregOf res; mkIntconv .Pmovsb_rr r r1 k
  | .Ocast8unsigned, [a1] => do
      let r1 ← iregOf a1; let r ← iregOf res; mkIntconv .Pmovzb_rr r r1 k
  | .Ocast16signed, [a1] => do
      let r1 ← iregOf a1; let r ← iregOf res; pure (.Pmovsw_rr r r1 :: k)
  | .Ocast16unsigned, [a1] => do
      let r1 ← iregOf a1; let r ← iregOf res; pure (.Pmovzw_rr r r1 :: k)
  | .Oneg, [a1] => iop1 a1 res .Pnegl k
  | .Osub, [a1, a2] => iop2 a1 a2 res .Psubl_rr k
  | .Omul, [a1, a2] => iop2 a1 a2 res .Pimull_rr k
  | .Omulimm n, [a1] => iop1 a1 res (fun r => .Pimull_ri r n) k
  | .Omulhs, [a1, a2] => mulh a1 a2 res .Pimull_r k
  | .Omulhu, [a1, a2] => mulh a1 a2 res .Pmull_r k
  | .Odiv, [a1, a2] => divop a1 a2 res .AX (.Pcltd :: .Pidivl .RCX :: k)
  | .Odivu, [a1, a2] => divop a1 a2 res .AX (.Pxorl_r .RDX :: .Pdivl .RCX :: k)
  | .Omod, [a1, a2] => divop a1 a2 res .DX (.Pcltd :: .Pidivl .RCX :: k)
  | .Omodu, [a1, a2] => divop a1 a2 res .DX (.Pxorl_r .RDX :: .Pdivl .RCX :: k)
  | .Oand, [a1, a2] => iop2 a1 a2 res .Pandl_rr k
  | .Oandimm n, [a1] => iop1 a1 res (fun r => .Pandl_ri r n) k
  | .Oor, [a1, a2] => iop2 a1 a2 res .Porl_rr k
  | .Oorimm n, [a1] => iop1 a1 res (fun r => .Porl_ri r n) k
  | .Oxor, [a1, a2] => iop2 a1 a2 res .Pxorl_rr k
  | .Oxorimm n, [a1] => iop1 a1 res (fun r => .Pxorl_ri r n) k
  | .Onot, [a1] => iop1 a1 res .Pnotl k
  | .Oshl, [a1, a2] => ishift a1 a2 res .Psall_rcl k
  | .Oshlimm n, [a1] => iop1 a1 res (fun r => .Psall_ri r n) k
  | .Oshr, [a1, a2] => ishift a1 a2 res .Psarl_rcl k
  | .Oshrimm n, [a1] => iop1 a1 res (fun r => .Psarl_ri r n) k
  | .Oshru, [a1, a2] => ishift a1 a2 res .Pshrl_rcl k
  | .Oshruimm n, [a1] => iop1 a1 res (fun r => .Pshrl_ri r n) k
  | .Oshrximm n, [a1] =>
      assert (decide (a1 = .AX)) (assert (decide (res = .AX)) (mkShrximm n k))
  | .Ororimm n, [a1] => iop1 a1 res (fun r => .Prorl_ri r n) k
  | .Oshldimm n, [a1, a2] => iop2 a1 a2 res (fun r r2 => .Pshld_ri r r2 n) k
  | .Olea addr, _ => do
      let am ← translAddressing addr args; let r ← iregOf res
      pure (.Pleal r (normalizeAddrmode32 am) :: k)
  -- 64-bit integer operations
  | .Olowlong, [a1] => iop1 a1 res .Pmovls_rr k
  | .Ocast32signed, [a1] => do
      let r1 ← iregOf a1; let r ← iregOf res; pure (.Pmovsl_rr r r1 :: k)
  | .Ocast32unsigned, [a1] => do
      let r1 ← iregOf a1; let r ← iregOf res; pure (.Pmovzl_rr r r1 :: k)
  | .Onegl, [a1] => iop1 a1 res .Pnegq k
  | .Oaddlimm n, [a1] => iop1 a1 res (fun r => .Paddq_ri r n) k
  | .Osubl, [a1, a2] => iop2 a1 a2 res .Psubq_rr k
  | .Omull, [a1, a2] => iop2 a1 a2 res .Pimulq_rr k
  | .Omullimm n, [a1] => iop1 a1 res (fun r => .Pimulq_ri r n) k
  | .Omullhs, [a1, a2] => mulh a1 a2 res .Pimulq_r k
  | .Omullhu, [a1, a2] => mulh a1 a2 res .Pmulq_r k
  | .Odivl, [a1, a2] => divop a1 a2 res .AX (.Pcqto :: .Pidivq .RCX :: k)
  | .Odivlu, [a1, a2] => divop a1 a2 res .AX (.Pxorq_r .RDX :: .Pdivq .RCX :: k)
  | .Omodl, [a1, a2] => divop a1 a2 res .DX (.Pcqto :: .Pidivq .RCX :: k)
  | .Omodlu, [a1, a2] => divop a1 a2 res .DX (.Pxorq_r .RDX :: .Pdivq .RCX :: k)
  | .Oandl, [a1, a2] => iop2 a1 a2 res .Pandq_rr k
  | .Oandlimm n, [a1] => iop1 a1 res (fun r => .Pandq_ri r n) k
  | .Oorl, [a1, a2] => iop2 a1 a2 res .Porq_rr k
  | .Oorlimm n, [a1] => iop1 a1 res (fun r => .Porq_ri r n) k
  | .Oxorl, [a1, a2] => iop2 a1 a2 res .Pxorq_rr k
  | .Oxorlimm n, [a1] => iop1 a1 res (fun r => .Pxorq_ri r n) k
  | .Onotl, [a1] => iop1 a1 res .Pnotq k
  | .Oshll, [a1, a2] => ishift a1 a2 res .Psalq_rcl k
  | .Oshllimm n, [a1] => iop1 a1 res (fun r => .Psalq_ri r n) k
  | .Oshrl, [a1, a2] => ishift a1 a2 res .Psarq_rcl k
  | .Oshrlimm n, [a1] => iop1 a1 res (fun r => .Psarq_ri r n) k
  | .Oshrxlimm n, [a1] =>
      assert (decide (a1 = .AX)) (assert (decide (res = .AX)) (mkShrxlimm n k))
  | .Oshrlu, [a1, a2] => ishift a1 a2 res .Pshrq_rcl k
  | .Oshrluimm n, [a1] => iop1 a1 res (fun r => .Pshrq_ri r n) k
  | .Ororlimm n, [a1] => iop1 a1 res (fun r => .Prorq_ri r n) k
  | .Oleal addr, _ => do
      let am ← translAddressing addr args; let r ← iregOf res
      pure (match normalizeAddrmode64 am with
        | (am', none) => .Pleaq r am' :: k
        | (am', some delta) => .Pleaq r am' :: .Paddq_ri r delta :: k)
  -- Floating-point operations
  | .Onegf, [a1] => fop1 a1 res .Pnegd k
  | .Oabsf, [a1] => fop1 a1 res .Pabsd k
  | .Oaddf, [a1, a2] => fop2 a1 a2 res .Paddd_ff k
  | .Osubf, [a1, a2] => fop2 a1 a2 res .Psubd_ff k
  | .Omulf, [a1, a2] => fop2 a1 a2 res .Pmuld_ff k
  | .Odivf, [a1, a2] => fop2 a1 a2 res .Pdivd_ff k
  | .Omaxf, [a1, a2] => fop2 a1 a2 res .Pmaxsd k
  | .Ominf, [a1, a2] => fop2 a1 a2 res .Pminsd k
  | .Onegfs, [a1] => fop1 a1 res .Pnegs k
  | .Oabsfs, [a1] => fop1 a1 res .Pabss k
  | .Oaddfs, [a1, a2] => fop2 a1 a2 res .Padds_ff k
  | .Osubfs, [a1, a2] => fop2 a1 a2 res .Psubs_ff k
  | .Omulfs, [a1, a2] => fop2 a1 a2 res .Pmuls_ff k
  | .Odivfs, [a1, a2] => fop2 a1 a2 res .Pdivs_ff k
  | .Osingleoffloat, [a1] => do
      let r ← fregOf res; let r1 ← fregOf a1; pure (.Pcvtsd2ss_ff r r1 :: k)
  | .Ofloatofsingle, [a1] => do
      let r ← fregOf res; let r1 ← fregOf a1; pure (.Pcvtss2sd_ff r r1 :: k)
  | .Ointoffloat, [a1] => do
      let r ← iregOf res; let r1 ← fregOf a1; pure (.Pcvttsd2si_rf r r1 :: k)
  | .Ofloatofint, [a1] => do
      let r ← fregOf res; let r1 ← iregOf a1; pure (.Pcvtsi2sd_fr r r1 :: k)
  | .Ointofsingle, [a1] => do
      let r ← iregOf res; let r1 ← fregOf a1; pure (.Pcvttss2si_rf r r1 :: k)
  | .Osingleofint, [a1] => do
      let r ← fregOf res; let r1 ← iregOf a1; pure (.Pcvtsi2ss_fr r r1 :: k)
  | .Olongoffloat, [a1] => do
      let r ← iregOf res; let r1 ← fregOf a1; pure (.Pcvttsd2sl_rf r r1 :: k)
  | .Ofloatoflong, [a1] => do
      let r ← fregOf res; let r1 ← iregOf a1; pure (.Pcvtsl2sd_fr r r1 :: k)
  | .Olongofsingle, [a1] => do
      let r ← iregOf res; let r1 ← fregOf a1; pure (.Pcvttss2sl_rf r r1 :: k)
  | .Osingleoflong, [a1] => do
      let r ← fregOf res; let r1 ← iregOf a1; pure (.Pcvtsl2ss_fr r r1 :: k)
  | .Ocmp c, args => do
      let r ← iregOf res
      translCond c args (mkSetcc (testcondForCondition c) r k)
  | .Osel c _, a1 :: a2 :: args =>
      assert (decide (a1 = res)) (do
        let r ← iregOf res; let r2 ← iregOf a2
        translSel c args r r2 k)
  | _, _ => .Error "Asmgen.transl_op"

/-! ## Loads and stores -/

/-- `Asmgen.transl_load` -/
def translLoad (chunk : Chunk) (addr : Addressing) (args : List Mreg) (dest : Mreg)
    (k : Code) : Res Code := do
  let am ← translAddressing addr args
  match chunk with
  | .Mint8unsigned => do let r ← iregOf dest; pure (.Pmovzb_rm r am :: k)
  | .Mint8signed => do let r ← iregOf dest; pure (.Pmovsb_rm r am :: k)
  | .Mint16unsigned => do let r ← iregOf dest; pure (.Pmovzw_rm r am :: k)
  | .Mint16signed => do let r ← iregOf dest; pure (.Pmovsw_rm r am :: k)
  | .Mint32 => do let r ← iregOf dest; pure (.Pmovl_rm r am :: k)
  | .Mint64 => do let r ← iregOf dest; pure (.Pmovq_rm r am :: k)
  | .Mfloat32 => do let r ← fregOf dest; pure (.Pmovss_fm r am :: k)
  | .Mfloat64 => do let r ← fregOf dest; pure (.Pmovsd_fm r am :: k)
  | _ => .Error "Asmgen.transl_load"

/-- `Asmgen.transl_store` -/
def translStore (chunk : Chunk) (addr : Addressing) (args : List Mreg) (src : Mreg)
    (k : Code) : Res Code := do
  let am ← translAddressing addr args
  match chunk with
  | .Mint8unsigned => do let r ← iregOf src; mkStorebyte am r k
  | .Mint16unsigned => do let r ← iregOf src; pure (.Pmovw_mr am r :: k)
  | .Mint32 => do let r ← iregOf src; pure (.Pmovl_mr am r :: k)
  | .Mint64 => do let r ← iregOf src; pure (.Pmovq_mr am r :: k)
  | .Mfloat32 => do let r ← fregOf src; pure (.Pmovss_mf am r :: k)
  | .Mfloat64 => do let r ← fregOf src; pure (.Pmovsd_mf am r :: k)
  | _ => .Error "Asmgen.transl_store"

/-! ## Instructions, code, functions, programs -/

/-- `Asmgen.transl_instr`.  `axIsParent`: does `RAX` still hold the
parent's stack pointer (set by `Pallocframe`)? -/
def translInstr (f : Mach.Function) (i : Mach.Instruction) (axIsParent : Bool) (k : Code) :
    Res Code :=
  match i with
  | .Mgetstack ofs ty dst => loadind .RSP ofs ty dst k
  | .Msetstack src ofs ty => storeind src .RSP ofs ty k
  | .Mgetparam ofs ty dst =>
      if axIsParent then loadind .RAX ofs ty dst k
      else do
        let k1 ← loadind .RAX ofs ty dst k
        loadind .RSP f.fn_link_ofs Tptr .AX k1
  | .Mop op args res => translOp op args res k
  | .Mload chunk addr args dst => translLoad chunk addr args dst k
  | .Mstore chunk addr args src => translStore chunk addr args src k
  | .Mcall sig (.inl reg) => do let r ← iregOf reg; pure (.Pcall_r r sig :: k)
  | .Mcall sig (.inr symb) => .OK (.Pcall_s symb sig :: k)
  | .Mtailcall sig (.inl reg) => do
      let r ← iregOf reg
      pure (.Pfreeframe f.fn_stacksize f.fn_retaddr_ofs f.fn_link_ofs :: .Pjmp_r r sig :: k)
  | .Mtailcall sig (.inr symb) =>
      .OK (.Pfreeframe f.fn_stacksize f.fn_retaddr_ofs f.fn_link_ofs :: .Pjmp_s symb sig :: k)
  | .Mlabel lbl => .OK (.Plabel lbl :: k)
  | .Mgoto lbl => .OK (.Pjmp_l lbl :: k)
  | .Mcond cond args lbl => translCond cond args (mkJcc (testcondForCondition cond) lbl k)
  | .Mjumptable arg tbl => do let r ← iregOf arg; pure (.Pjmptbl r tbl :: k)
  | .Mreturn =>
      .OK (.Pfreeframe f.fn_stacksize f.fn_retaddr_ofs f.fn_link_ofs :: .Pret :: k)
  | .Mbuiltin ef args res =>
      .OK (.Pbuiltin ef (args.map (BuiltinArg.map pregOf)) (BuiltinRes.map pregOf res) :: k)

/-- `Asmgen.it1_is_parent` -/
def it1IsParent (before : Bool) (i : Mach.Instruction) : Bool :=
  match i with
  | .Msetstack .. => before
  | .Mgetparam _ _ dst => !(decide (dst = .AX))
  | _ => false

/-- `Asmgen.transl_code`: the naive (non-tail-recursive) translation, kept
as specification. -/
def translCode (f : Mach.Function) : List Mach.Instruction → Bool → Res Code
  | [], _ => .OK []
  | i1 :: il', axp => do
      let k ← translCode f il' (it1IsParent axp i1)
      translInstr f i1 axp k

/-- `Asmgen.transl_code_rec`: the same in continuation-passing style. -/
def translCodeRec (f : Mach.Function) :
    List Mach.Instruction → Bool → (Code → Res Code) → Res Code
  | [], _, k => k []
  | i1 :: il', axp, k =>
      translCodeRec f il' (it1IsParent axp i1)
        (fun c1 => do let c2 ← translInstr f i1 axp c1; k c2)

/-- `Asmgen.transl_code'` -/
def translCode' (f : Mach.Function) (il : List Mach.Instruction) (axp : Bool) : Res Code :=
  translCodeRec f il axp (fun c => .OK c)

/-- `Asmgen.transl_function` -/
def translFunction (f : Mach.Function) : Res Asm.Function := do
  let c ← translCode' f f.fn_code true
  pure { fn_sig := f.fn_sig,
         fn_code := .Pallocframe f.fn_stacksize f.fn_retaddr_ofs f.fn_link_ofs :: c }

/-- `Asmgen.transf_function`: also checks that the code has fewer than
`2^64` instructions, so that the offset part of `PC` cannot wrap around. -/
def transfFunction (f : Mach.Function) : Res Asm.Function := do
  let tf ← translFunction f
  if Integers.Ptrofs.max_unsigned < (tf.fn_code.length : Z) then .Error "code size exceeded"
  else pure tf

/-- `Asmgen.transf_fundef` -/
def transfFundef (f : Mach.Fundef) : Res Asm.Fundef :=
  ASTFundef.transfPartial transfFunction f

/-- `Asmgen.transf_program` -/
def transfProgram (p : Mach.Program) : Res Asm.Program :=
  transformPartialProgram transfFundef p

/-! ## Equivalence of the two code translations (`Asmgenproof.v`) -/

private theorem translCodeRec_spec (f : Mach.Function) :
    ∀ (il : List Mach.Instruction) (axp : Bool) (k : Code → Res Code),
      translCodeRec f il axp k = Res.bind (translCode f il axp) k
  | [], _, k => rfl
  | i1 :: il', axp, k => by
      rw [translCodeRec, translCodeRec_spec f il']
      simp only [translCode]
      show _ = Res.bind (Res.bind _ _) _
      cases translCode f il' (it1IsParent axp i1) with
      | OK a => rfl
      | Error m => rfl

/-- `Asmgenproof.transl_code'_transl_code` -/
theorem transl_code'_transl_code (f : Mach.Function) (il : List Mach.Instruction)
    (axp : Bool) : translCode' f il axp = translCode f il axp := by
  rw [translCode', translCodeRec_spec]
  cases translCode f il axp <;> rfl

end Asmgen
end X86
end CC
