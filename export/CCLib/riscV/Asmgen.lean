/-
  Translation from Mach to RISC-V assembly — port of `riscV/Asmgen.v`
  (whole file).

  Ported: `ireg_of`, `freg_of`, `immed32`, `make_immed32`, `immed64`,
  `make_immed64`, `load_hilo32`, `loadimm32`, `opimm32` and its instances,
  `load_hilo64`, `loadimm64`, `opimm64` and its instances, `addptrofs`,
  `transl_cbranch_int32s/32u/64s/64u`, `transl_cond_float`,
  `transl_cond_single`, `transl_cbranch`, `transl_cond_int32s/32u/64s/64u`,
  `transl_condimm_int32s/32u/64s/64u`, `transl_cond_op`, `transl_op`,
  `indexed_memory_access`, `loadind`, `storeind`, `loadind_ptr`,
  `storeind_ptr`, `transl_memory_access`, `transl_load`, `transl_store`,
  `make_epilogue`, `transl_instr`, `it1_is_parent`, `transl_code`,
  `transl_code_rec`, `transl_code'`, `transl_function`, `transf_function`,
  `transf_fundef`, `transf_program`.
  Also proved: `transl_code'_transl_code` (from `Asmgenproof.v`).

  Differences from Rocq: the OCaml parameter `SelectOp.symbol_is_relocatable`
  is a field of an explicit `Options` argument (default: no symbol is
  relocatable); `assertion b; k` is `assert b k`; error messages are plain
  strings.
-/
import CCLib.riscV.Asm
import CCLib.riscV.Mach

namespace CC
namespace RiscV
namespace Asmgen

open Asm Op

/-- The OCaml parameters used by Asmgen. -/
structure Options where
  /-- `SelectOp.symbol_is_relocatable` -/
  symbolIsRelocatable : Ident → Bool := fun _ => false

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

/-! ## Decomposition of integer constants -/

/-- `Asmgen.immed32`: a 12-bit signed immediate, or a (20-bit high,
12-bit low) pair. -/
inductive Immed32 where
  | Imm32_single (imm : Integers.Int)
  | Imm32_pair (hi lo : Integers.Int)

/-- `Asmgen.make_immed32` -/
def makeImmed32 (val : Integers.Int) : Immed32 :=
  let lo := Integers.Int.sign_ext 12 val
  if Integers.Int.eq val lo then .Imm32_single val
  else .Imm32_pair (Integers.Int.shru (Integers.Int.sub val lo) (Integers.Int.repr 12)) lo

/-- `Asmgen.immed64` -/
inductive Immed64 where
  | Imm64_single (imm : Integers.Int64)
  | Imm64_pair (hi lo : Integers.Int64)
  | Imm64_large (imm : Integers.Int64)

/-- `Asmgen.make_immed64` -/
def makeImmed64 (val : Integers.Int64) : Immed64 :=
  let lo := Integers.Int64.sign_ext 12 val
  if Integers.Int64.eq val lo then .Imm64_single lo else
  let hi := Integers.Int64.zero_ext 20
    (Integers.Int64.shru (Integers.Int64.sub val lo) (Integers.Int64.repr 12))
  if Integers.Int64.eq val (Integers.Int64.add
      (Integers.Int64.sign_ext 32 (Integers.Int64.shl hi (Integers.Int64.repr 12))) lo)
  then .Imm64_pair hi lo
  else .Imm64_large val

/-! ## Smart constructors for operations with an integer constant -/

/-- `Asmgen.load_hilo32` -/
def loadHilo32 (r : Ireg) (hi lo : Integers.Int) (k : Code) : Code :=
  if Integers.Int.eq lo Integers.Int.zero then .Pluiw r hi :: k
  else .Pluiw r hi :: .Paddiw r r lo :: k

/-- `Asmgen.loadimm32` -/
def loadimm32 (r : Ireg) (n : Integers.Int) (k : Code) : Code :=
  match makeImmed32 n with
  | .Imm32_single imm => .Paddiw r .X0 imm :: k
  | .Imm32_pair hi lo => loadHilo32 r hi lo k

/-- `Asmgen.opimm32` -/
def opimm32 (op : Ireg → Ireg0 → Ireg0 → Instruction)
    (opimm : Ireg → Ireg0 → Integers.Int → Instruction)
    (rd rs : Ireg) (n : Integers.Int) (k : Code) : Code :=
  match makeImmed32 n with
  | .Imm32_single imm => opimm rd rs imm :: k
  | .Imm32_pair hi lo => loadHilo32 Ireg.X31 hi lo (op rd rs Ireg.X31 :: k)

/-- `Asmgen.addimm32` -/
def addimm32 : Ireg → Ireg → Integers.Int → Code → Code := opimm32 .Paddw .Paddiw
/-- `Asmgen.andimm32` -/
def andimm32 : Ireg → Ireg → Integers.Int → Code → Code := opimm32 .Pandw .Pandiw
/-- `Asmgen.orimm32` -/
def orimm32 : Ireg → Ireg → Integers.Int → Code → Code := opimm32 .Porw .Poriw
/-- `Asmgen.xorimm32` -/
def xorimm32 : Ireg → Ireg → Integers.Int → Code → Code := opimm32 .Pxorw .Pxoriw
/-- `Asmgen.sltimm32` -/
def sltimm32 : Ireg → Ireg → Integers.Int → Code → Code := opimm32 .Psltw .Psltiw
/-- `Asmgen.sltuimm32` -/
def sltuimm32 : Ireg → Ireg → Integers.Int → Code → Code := opimm32 .Psltuw .Psltiuw

/-- `Asmgen.load_hilo64` -/
def loadHilo64 (r : Ireg) (hi lo : Integers.Int64) (k : Code) : Code :=
  if Integers.Int64.eq lo Integers.Int64.zero then .Pluil r hi :: k
  else .Pluil r hi :: .Paddil r r lo :: k

/-- `Asmgen.loadimm64` -/
def loadimm64 (r : Ireg) (n : Integers.Int64) (k : Code) : Code :=
  match makeImmed64 n with
  | .Imm64_single imm => .Paddil r .X0 imm :: k
  | .Imm64_pair hi lo => loadHilo64 r hi lo k
  | .Imm64_large imm => .Ploadli r imm :: k

/-- `Asmgen.opimm64` -/
def opimm64 (op : Ireg → Ireg0 → Ireg0 → Instruction)
    (opimm : Ireg → Ireg0 → Integers.Int64 → Instruction)
    (rd rs : Ireg) (n : Integers.Int64) (k : Code) : Code :=
  match makeImmed64 n with
  | .Imm64_single imm => opimm rd rs imm :: k
  | .Imm64_pair hi lo => loadHilo64 Ireg.X31 hi lo (op rd rs Ireg.X31 :: k)
  | .Imm64_large imm => .Ploadli Ireg.X31 imm :: op rd rs Ireg.X31 :: k

/-- `Asmgen.addimm64` -/
def addimm64 : Ireg → Ireg → Integers.Int64 → Code → Code := opimm64 .Paddl .Paddil
/-- `Asmgen.andimm64` -/
def andimm64 : Ireg → Ireg → Integers.Int64 → Code → Code := opimm64 .Pandl .Pandil
/-- `Asmgen.orimm64` -/
def orimm64 : Ireg → Ireg → Integers.Int64 → Code → Code := opimm64 .Porl .Poril
/-- `Asmgen.xorimm64` -/
def xorimm64 : Ireg → Ireg → Integers.Int64 → Code → Code := opimm64 .Pxorl .Pxoril
/-- `Asmgen.sltimm64` -/
def sltimm64 : Ireg → Ireg → Integers.Int64 → Code → Code := opimm64 .Psltl .Psltil
/-- `Asmgen.sltuimm64` -/
def sltuimm64 : Ireg → Ireg → Integers.Int64 → Code → Code := opimm64 .Psltul .Psltiul

/-- `Asmgen.addptrofs` -/
def addptrofs (rd rs : Ireg) (n : Integers.Ptrofs) (k : Code) : Code :=
  if n = Integers.Ptrofs.zero then .Pmv rd rs :: k
  else if Archi.ptr64 then addimm64 rd rs (Integers.Ptrofs.to_int64 n) k
  else addimm32 rd rs (Integers.Ptrofs.to_int n) k

/-! ## Conditional branches -/

/-- `Asmgen.transl_cbranch_int32s` -/
def translCbranchInt32s (cmp : Comparison) (r1 r2 : Ireg0) (lbl : Label) : Instruction :=
  match cmp with
  | .Ceq => .Pbeqw r1 r2 lbl
  | .Cne => .Pbnew r1 r2 lbl
  | .Clt => .Pbltw r1 r2 lbl
  | .Cle => .Pbgew r2 r1 lbl
  | .Cgt => .Pbltw r2 r1 lbl
  | .Cge => .Pbgew r1 r2 lbl

/-- `Asmgen.transl_cbranch_int32u` -/
def translCbranchInt32u (cmp : Comparison) (r1 r2 : Ireg0) (lbl : Label) : Instruction :=
  match cmp with
  | .Ceq => .Pbeqw r1 r2 lbl
  | .Cne => .Pbnew r1 r2 lbl
  | .Clt => .Pbltuw r1 r2 lbl
  | .Cle => .Pbgeuw r2 r1 lbl
  | .Cgt => .Pbltuw r2 r1 lbl
  | .Cge => .Pbgeuw r1 r2 lbl

/-- `Asmgen.transl_cbranch_int64s` -/
def translCbranchInt64s (cmp : Comparison) (r1 r2 : Ireg0) (lbl : Label) : Instruction :=
  match cmp with
  | .Ceq => .Pbeql r1 r2 lbl
  | .Cne => .Pbnel r1 r2 lbl
  | .Clt => .Pbltl r1 r2 lbl
  | .Cle => .Pbgel r2 r1 lbl
  | .Cgt => .Pbltl r2 r1 lbl
  | .Cge => .Pbgel r1 r2 lbl

/-- `Asmgen.transl_cbranch_int64u` -/
def translCbranchInt64u (cmp : Comparison) (r1 r2 : Ireg0) (lbl : Label) : Instruction :=
  match cmp with
  | .Ceq => .Pbeql r1 r2 lbl
  | .Cne => .Pbnel r1 r2 lbl
  | .Clt => .Pbltul r1 r2 lbl
  | .Cle => .Pbgeul r2 r1 lbl
  | .Cgt => .Pbltul r2 r1 lbl
  | .Cge => .Pbgeul r1 r2 lbl

/-- `Asmgen.transl_cond_float`: the instruction, and whether its result is
the condition (`true`) or its negation (`false`). -/
def translCondFloat (cmp : Comparison) (rd : Ireg) (fs1 fs2 : Freg) : Instruction × Bool :=
  match cmp with
  | .Ceq => (.Pfeqd rd fs1 fs2, true)
  | .Cne => (.Pfeqd rd fs1 fs2, false)
  | .Clt => (.Pfltd rd fs1 fs2, true)
  | .Cle => (.Pfled rd fs1 fs2, true)
  | .Cgt => (.Pfltd rd fs2 fs1, true)
  | .Cge => (.Pfled rd fs2 fs1, true)

/-- `Asmgen.transl_cond_single` -/
def translCondSingle (cmp : Comparison) (rd : Ireg) (fs1 fs2 : Freg) : Instruction × Bool :=
  match cmp with
  | .Ceq => (.Pfeqs rd fs1 fs2, true)
  | .Cne => (.Pfeqs rd fs1 fs2, false)
  | .Clt => (.Pflts rd fs1 fs2, true)
  | .Cle => (.Pfles rd fs1 fs2, true)
  | .Cgt => (.Pflts rd fs2 fs1, true)
  | .Cge => (.Pfles rd fs2 fs1, true)

/-- `Asmgen.transl_cbranch` -/
def translCbranch (cond : Condition) (args : List Mreg) (lbl : Label) (k : Code) : Res Code :=
  match cond, args with
  | .Ccomp c, [a1, a2] => do
      let r1 ← iregOf a1
      let r2 ← iregOf a2
      pure (translCbranchInt32s c r1 r2 lbl :: k)
  | .Ccompu c, [a1, a2] => do
      let r1 ← iregOf a1
      let r2 ← iregOf a2
      pure (translCbranchInt32u c r1 r2 lbl :: k)
  | .Ccompl c, [a1, a2] => do
      let r1 ← iregOf a1
      let r2 ← iregOf a2
      pure (translCbranchInt64s c r1 r2 lbl :: k)
  | .Ccomplu c, [a1, a2] => do
      let r1 ← iregOf a1
      let r2 ← iregOf a2
      pure (translCbranchInt64u c r1 r2 lbl :: k)
  | .Ccompimm c n, [a1] => do
      let r1 ← iregOf a1
      pure (if Integers.Int.eq n Integers.Int.zero then translCbranchInt32s c r1 .X0 lbl :: k
            else loadimm32 Ireg.X31 n (translCbranchInt32s c r1 Ireg.X31 lbl :: k))
  | .Ccompuimm c n, [a1] => do
      let r1 ← iregOf a1
      pure (if Integers.Int.eq n Integers.Int.zero then translCbranchInt32u c r1 .X0 lbl :: k
            else loadimm32 Ireg.X31 n (translCbranchInt32u c r1 Ireg.X31 lbl :: k))
  | .Ccomplimm c n, [a1] => do
      let r1 ← iregOf a1
      pure (if Integers.Int64.eq n Integers.Int64.zero then translCbranchInt64s c r1 .X0 lbl :: k
            else loadimm64 Ireg.X31 n (translCbranchInt64s c r1 Ireg.X31 lbl :: k))
  | .Ccompluimm c n, [a1] => do
      let r1 ← iregOf a1
      pure (if Integers.Int64.eq n Integers.Int64.zero then translCbranchInt64u c r1 .X0 lbl :: k
            else loadimm64 Ireg.X31 n (translCbranchInt64u c r1 Ireg.X31 lbl :: k))
  | .Ccompf c, [f1, f2] => do
      let r1 ← fregOf f1
      let r2 ← fregOf f2
      let (insn, normal) := translCondFloat c Ireg.X31 r1 r2
      pure (insn :: (if normal then .Pbnew Ireg.X31 .X0 lbl else .Pbeqw Ireg.X31 .X0 lbl) :: k)
  | .Cnotcompf c, [f1, f2] => do
      let r1 ← fregOf f1
      let r2 ← fregOf f2
      let (insn, normal) := translCondFloat c Ireg.X31 r1 r2
      pure (insn :: (if normal then .Pbeqw Ireg.X31 .X0 lbl else .Pbnew Ireg.X31 .X0 lbl) :: k)
  | .Ccompfs c, [f1, f2] => do
      let r1 ← fregOf f1
      let r2 ← fregOf f2
      let (insn, normal) := translCondSingle c Ireg.X31 r1 r2
      pure (insn :: (if normal then .Pbnew Ireg.X31 .X0 lbl else .Pbeqw Ireg.X31 .X0 lbl) :: k)
  | .Cnotcompfs c, [f1, f2] => do
      let r1 ← fregOf f1
      let r2 ← fregOf f2
      let (insn, normal) := translCondSingle c Ireg.X31 r1 r2
      pure (insn :: (if normal then .Pbeqw Ireg.X31 .X0 lbl else .Pbnew Ireg.X31 .X0 lbl) :: k)
  | _, _ => .Error "Asmgen.transl_cond_branch"

/-! ## Condition operators -/

/-- `Asmgen.transl_cond_int32s` -/
def translCondInt32s (cmp : Comparison) (rd : Ireg) (r1 r2 : Ireg0) (k : Code) : Code :=
  match cmp with
  | .Ceq => .Pseqw rd r1 r2 :: k
  | .Cne => .Psnew rd r1 r2 :: k
  | .Clt => .Psltw rd r1 r2 :: k
  | .Cle => .Psltw rd r2 r1 :: .Pxoriw rd rd Integers.Int.one :: k
  | .Cgt => .Psltw rd r2 r1 :: k
  | .Cge => .Psltw rd r1 r2 :: .Pxoriw rd rd Integers.Int.one :: k

/-- `Asmgen.transl_cond_int32u` -/
def translCondInt32u (cmp : Comparison) (rd : Ireg) (r1 r2 : Ireg0) (k : Code) : Code :=
  match cmp with
  | .Ceq => .Pseqw rd r1 r2 :: k
  | .Cne => .Psnew rd r1 r2 :: k
  | .Clt => .Psltuw rd r1 r2 :: k
  | .Cle => .Psltuw rd r2 r1 :: .Pxoriw rd rd Integers.Int.one :: k
  | .Cgt => .Psltuw rd r2 r1 :: k
  | .Cge => .Psltuw rd r1 r2 :: .Pxoriw rd rd Integers.Int.one :: k

/-- `Asmgen.transl_cond_int64s` -/
def translCondInt64s (cmp : Comparison) (rd : Ireg) (r1 r2 : Ireg0) (k : Code) : Code :=
  match cmp with
  | .Ceq => .Pseql rd r1 r2 :: k
  | .Cne => .Psnel rd r1 r2 :: k
  | .Clt => .Psltl rd r1 r2 :: k
  | .Cle => .Psltl rd r2 r1 :: .Pxoriw rd rd Integers.Int.one :: k
  | .Cgt => .Psltl rd r2 r1 :: k
  | .Cge => .Psltl rd r1 r2 :: .Pxoriw rd rd Integers.Int.one :: k

/-- `Asmgen.transl_cond_int64u` -/
def translCondInt64u (cmp : Comparison) (rd : Ireg) (r1 r2 : Ireg0) (k : Code) : Code :=
  match cmp with
  | .Ceq => .Pseql rd r1 r2 :: k
  | .Cne => .Psnel rd r1 r2 :: k
  | .Clt => .Psltul rd r1 r2 :: k
  | .Cle => .Psltul rd r2 r1 :: .Pxoriw rd rd Integers.Int.one :: k
  | .Cgt => .Psltul rd r2 r1 :: k
  | .Cge => .Psltul rd r1 r2 :: .Pxoriw rd rd Integers.Int.one :: k

/-- `Asmgen.transl_condimm_int32s` -/
def translCondimmInt32s (cmp : Comparison) (rd r1 : Ireg) (n : Integers.Int) (k : Code) : Code :=
  if Integers.Int.eq n Integers.Int.zero then translCondInt32s cmp rd r1 .X0 k else
  match cmp with
  | .Ceq | .Cne => xorimm32 rd r1 n (translCondInt32s cmp rd rd .X0 k)
  | .Clt => sltimm32 rd r1 n k
  | .Cle =>
      if Integers.Int.eq n (Integers.Int.repr Integers.Int.max_signed)
      then loadimm32 rd Integers.Int.one k
      else sltimm32 rd r1 (Integers.Int.add n Integers.Int.one) k
  | _ => loadimm32 Ireg.X31 n (translCondInt32s cmp rd r1 Ireg.X31 k)

/-- `Asmgen.transl_condimm_int32u` -/
def translCondimmInt32u (cmp : Comparison) (rd r1 : Ireg) (n : Integers.Int) (k : Code) : Code :=
  if Integers.Int.eq n Integers.Int.zero then translCondInt32u cmp rd r1 .X0 k else
  match cmp with
  | .Clt => sltuimm32 rd r1 n k
  | _ => loadimm32 Ireg.X31 n (translCondInt32u cmp rd r1 Ireg.X31 k)

/-- `Asmgen.transl_condimm_int64s` -/
def translCondimmInt64s (cmp : Comparison) (rd r1 : Ireg) (n : Integers.Int64) (k : Code) :
    Code :=
  if Integers.Int64.eq n Integers.Int64.zero then translCondInt64s cmp rd r1 .X0 k else
  match cmp with
  | .Ceq | .Cne => xorimm64 rd r1 n (translCondInt64s cmp rd rd .X0 k)
  | .Clt => sltimm64 rd r1 n k
  | .Cle =>
      if Integers.Int64.eq n (Integers.Int64.repr Integers.Int64.max_signed)
      then loadimm32 rd Integers.Int.one k
      else sltimm64 rd r1 (Integers.Int64.add n Integers.Int64.one) k
  | _ => loadimm64 Ireg.X31 n (translCondInt64s cmp rd r1 Ireg.X31 k)

/-- `Asmgen.transl_condimm_int64u` -/
def translCondimmInt64u (cmp : Comparison) (rd r1 : Ireg) (n : Integers.Int64) (k : Code) :
    Code :=
  if Integers.Int64.eq n Integers.Int64.zero then translCondInt64u cmp rd r1 .X0 k else
  match cmp with
  | .Clt => sltuimm64 rd r1 n k
  | _ => loadimm64 Ireg.X31 n (translCondInt64u cmp rd r1 Ireg.X31 k)

/-- `Asmgen.transl_cond_op`: set `rd` to 0 or 1 according to the condition. -/
def translCondOp (cond : Condition) (rd : Ireg) (args : List Mreg) (k : Code) : Res Code :=
  match cond, args with
  | .Ccomp c, [a1, a2] => do
      let r1 ← iregOf a1
      let r2 ← iregOf a2
      pure (translCondInt32s c rd r1 r2 k)
  | .Ccompu c, [a1, a2] => do
      let r1 ← iregOf a1
      let r2 ← iregOf a2
      pure (translCondInt32u c rd r1 r2 k)
  | .Ccompl c, [a1, a2] => do
      let r1 ← iregOf a1
      let r2 ← iregOf a2
      pure (translCondInt64s c rd r1 r2 k)
  | .Ccomplu c, [a1, a2] => do
      let r1 ← iregOf a1
      let r2 ← iregOf a2
      pure (translCondInt64u c rd r1 r2 k)
  | .Ccompimm c n, [a1] => do
      let r1 ← iregOf a1
      pure (translCondimmInt32s c rd r1 n k)
  | .Ccompuimm c n, [a1] => do
      let r1 ← iregOf a1
      pure (translCondimmInt32u c rd r1 n k)
  | .Ccomplimm c n, [a1] => do
      let r1 ← iregOf a1
      pure (translCondimmInt64s c rd r1 n k)
  | .Ccompluimm c n, [a1] => do
      let r1 ← iregOf a1
      pure (translCondimmInt64u c rd r1 n k)
  | .Ccompf c, [f1, f2] => do
      let r1 ← fregOf f1
      let r2 ← fregOf f2
      let (insn, normal) := translCondFloat c rd r1 r2
      pure (insn :: if normal then k else .Pxoriw rd rd Integers.Int.one :: k)
  | .Cnotcompf c, [f1, f2] => do
      let r1 ← fregOf f1
      let r2 ← fregOf f2
      let (insn, normal) := translCondFloat c rd r1 r2
      pure (insn :: if normal then .Pxoriw rd rd Integers.Int.one :: k else k)
  | .Ccompfs c, [f1, f2] => do
      let r1 ← fregOf f1
      let r2 ← fregOf f2
      let (insn, normal) := translCondSingle c rd r1 r2
      pure (insn :: if normal then k else .Pxoriw rd rd Integers.Int.one :: k)
  | .Cnotcompfs c, [f1, f2] => do
      let r1 ← fregOf f1
      let r2 ← fregOf f2
      let (insn, normal) := translCondSingle c rd r1 r2
      pure (insn :: if normal then .Pxoriw rd rd Integers.Int.one :: k else k)
  | _, _ => .Error "Asmgen.transl_cond_op"

/-! ## Arithmetic operations -/

/-- `Asmgen.transl_op` -/
def translOp (o : Options) (op : Operation) (args : List Mreg) (res : Mreg) (k : Code) :
    Res Code :=
  match op, args with
  | .Omove, [a1] =>
      match pregOf res, pregOf a1 with
      | .IR r, .IR a => .OK (.Pmv r a :: k)
      | .FR r, .FR a => .OK (.Pfmv r a :: k)
      | _, _ => .Error "Asmgen.Omove"
  | .Ointconst n, [] => do
      let rd ← iregOf res
      pure (loadimm32 rd n k)
  | .Olongconst n, [] => do
      let rd ← iregOf res
      pure (loadimm64 rd n k)
  | .Ofloatconst f, [] => do
      let rd ← fregOf res
      pure (if f = Floats.Float.zero then .Pfcvtdw rd .X0 :: k else .Ploadfi rd f :: k)
  | .Osingleconst f, [] => do
      let rd ← fregOf res
      pure (if f = Floats.Float32.zero then .Pfcvtsw rd .X0 :: k else .Ploadsi rd f :: k)
  | .Oaddrsymbol s ofs, [] => do
      let rd ← iregOf res
      pure (if o.symbolIsRelocatable s && !(Integers.Ptrofs.eq ofs Integers.Ptrofs.zero)
            then .Ploadsymbol rd s Integers.Ptrofs.zero :: addptrofs rd rd ofs k
            else .Ploadsymbol rd s ofs :: k)
  | .Oaddrstack n, [] => do
      let rd ← iregOf res
      pure (addptrofs rd SP n k)
  | .Oshrximm n, [a1] => do
      let rd ← iregOf res
      let rs ← iregOf a1
      pure (if Integers.Int.eq n Integers.Int.zero then .Pmv rd rs :: k else
            .Psraiw Ireg.X31 rs (Integers.Int.repr 31) ::
            .Psrliw Ireg.X31 Ireg.X31 (Integers.Int.sub Integers.Int.iwordsize n) ::
            .Paddw Ireg.X31 rs Ireg.X31 ::
            .Psraiw rd Ireg.X31 n :: k)
  | .Ocast32signed, [a1] => do
      let rd ← iregOf res
      let rs ← iregOf a1
      assert (decide (rd = rs)) (pure (.Pcvtw2l rd :: k))
  | .Ocast32unsigned, [a1] => do
      let rd ← iregOf res
      let rs ← iregOf a1
      assert (decide (rd = rs))
        (pure (.Pcvtw2l rd :: .Psllil rd rd (Integers.Int.repr 32) ::
               .Psrlil rd rd (Integers.Int.repr 32) :: k))
  | .Oshrxlimm n, [a1] => do
      let rd ← iregOf res
      let rs ← iregOf a1
      pure (if Integers.Int.eq n Integers.Int.zero then .Pmv rd rs :: k else
            .Psrail Ireg.X31 rs (Integers.Int.repr 63) ::
            .Psrlil Ireg.X31 Ireg.X31 (Integers.Int.sub Integers.Int64.iwordsize' n) ::
            .Paddl Ireg.X31 rs Ireg.X31 ::
            .Psrail rd Ireg.X31 n :: k)
  | .Ocmp cmp, _ => do
      let rd ← iregOf res
      translCondOp cmp rd args k
  | .Osel cmp _, a1 :: a2 :: args => do
      let rd ← iregOf res
      let rs1 ← iregOf a1
      let rs2 ← iregOf a2
      if rs1 = rs2 then pure (.Pmv rd rs1 :: k)
      else translCondOp cmp Ireg.X31 args (.Pcsel rd Ireg.X31 rs1 rs2 :: k)
  | .Ocast8signed, [a1] => do
      let rd ← iregOf res
      let rs ← iregOf a1
      pure (.Pslliw rd rs (Integers.Int.repr 24) :: .Psraiw rd rd (Integers.Int.repr 24) :: k)
  | .Ocast16signed, [a1] => do
      let rd ← iregOf res
      let rs ← iregOf a1
      pure (.Pslliw rd rs (Integers.Int.repr 16) :: .Psraiw rd rd (Integers.Int.repr 16) :: k)
  | .Oadd, [a1, a2] => do
      let rd ← iregOf res
      let rs1 ← iregOf a1
      let rs2 ← iregOf a2
      pure (.Paddw rd rs1 rs2 :: k)
  | .Oaddimm n, [a1] => do
      let rd ← iregOf res
      let rs ← iregOf a1
      pure (addimm32 rd rs n k)
  | .Oneg, [a1] => do
      let rd ← iregOf res
      let rs ← iregOf a1
      pure (.Psubw rd .X0 rs :: k)
  | .Osub, [a1, a2] => do
      let rd ← iregOf res
      let rs1 ← iregOf a1
      let rs2 ← iregOf a2
      pure (.Psubw rd rs1 rs2 :: k)
  | .Omul, [a1, a2] => do
      let rd ← iregOf res
      let rs1 ← iregOf a1
      let rs2 ← iregOf a2
      pure (.Pmulw rd rs1 rs2 :: k)
  | .Omulhs, [a1, a2] => do
      let rd ← iregOf res
      let rs1 ← iregOf a1
      let rs2 ← iregOf a2
      pure (.Pmulhw rd rs1 rs2 :: k)
  | .Omulhu, [a1, a2] => do
      let rd ← iregOf res
      let rs1 ← iregOf a1
      let rs2 ← iregOf a2
      pure (.Pmulhuw rd rs1 rs2 :: k)
  | .Odiv, [a1, a2] => do
      let rd ← iregOf res
      let rs1 ← iregOf a1
      let rs2 ← iregOf a2
      pure (.Pdivw rd rs1 rs2 :: k)
  | .Odivu, [a1, a2] => do
      let rd ← iregOf res
      let rs1 ← iregOf a1
      let rs2 ← iregOf a2
      pure (.Pdivuw rd rs1 rs2 :: k)
  | .Omod, [a1, a2] => do
      let rd ← iregOf res
      let rs1 ← iregOf a1
      let rs2 ← iregOf a2
      pure (.Premw rd rs1 rs2 :: k)
  | .Omodu, [a1, a2] => do
      let rd ← iregOf res
      let rs1 ← iregOf a1
      let rs2 ← iregOf a2
      pure (.Premuw rd rs1 rs2 :: k)
  | .Oand, [a1, a2] => do
      let rd ← iregOf res
      let rs1 ← iregOf a1
      let rs2 ← iregOf a2
      pure (.Pandw rd rs1 rs2 :: k)
  | .Oandimm n, [a1] => do
      let rd ← iregOf res
      let rs ← iregOf a1
      pure (andimm32 rd rs n k)
  | .Oor, [a1, a2] => do
      let rd ← iregOf res
      let rs1 ← iregOf a1
      let rs2 ← iregOf a2
      pure (.Porw rd rs1 rs2 :: k)
  | .Oorimm n, [a1] => do
      let rd ← iregOf res
      let rs ← iregOf a1
      pure (orimm32 rd rs n k)
  | .Oxor, [a1, a2] => do
      let rd ← iregOf res
      let rs1 ← iregOf a1
      let rs2 ← iregOf a2
      pure (.Pxorw rd rs1 rs2 :: k)
  | .Oxorimm n, [a1] => do
      let rd ← iregOf res
      let rs ← iregOf a1
      pure (xorimm32 rd rs n k)
  | .Oshl, [a1, a2] => do
      let rd ← iregOf res
      let rs1 ← iregOf a1
      let rs2 ← iregOf a2
      pure (.Psllw rd rs1 rs2 :: k)
  | .Oshlimm n, [a1] => do
      let rd ← iregOf res
      let rs ← iregOf a1
      pure (.Pslliw rd rs n :: k)
  | .Oshr, [a1, a2] => do
      let rd ← iregOf res
      let rs1 ← iregOf a1
      let rs2 ← iregOf a2
      pure (.Psraw rd rs1 rs2 :: k)
  | .Oshrimm n, [a1] => do
      let rd ← iregOf res
      let rs ← iregOf a1
      pure (.Psraiw rd rs n :: k)
  | .Oshru, [a1, a2] => do
      let rd ← iregOf res
      let rs1 ← iregOf a1
      let rs2 ← iregOf a2
      pure (.Psrlw rd rs1 rs2 :: k)
  | .Oshruimm n, [a1] => do
      let rd ← iregOf res
      let rs ← iregOf a1
      pure (.Psrliw rd rs n :: k)
  | .Olowlong, [a1] => do
      let rd ← iregOf res
      let rs ← iregOf a1
      pure (.Pcvtl2w rd rs :: k)
  | .Oaddl, [a1, a2] => do
      let rd ← iregOf res
      let rs1 ← iregOf a1
      let rs2 ← iregOf a2
      pure (.Paddl rd rs1 rs2 :: k)
  | .Oaddlimm n, [a1] => do
      let rd ← iregOf res
      let rs ← iregOf a1
      pure (addimm64 rd rs n k)
  | .Onegl, [a1] => do
      let rd ← iregOf res
      let rs ← iregOf a1
      pure (.Psubl rd .X0 rs :: k)
  | .Osubl, [a1, a2] => do
      let rd ← iregOf res
      let rs1 ← iregOf a1
      let rs2 ← iregOf a2
      pure (.Psubl rd rs1 rs2 :: k)
  | .Omull, [a1, a2] => do
      let rd ← iregOf res
      let rs1 ← iregOf a1
      let rs2 ← iregOf a2
      pure (.Pmull rd rs1 rs2 :: k)
  | .Omullhs, [a1, a2] => do
      let rd ← iregOf res
      let rs1 ← iregOf a1
      let rs2 ← iregOf a2
      pure (.Pmulhl rd rs1 rs2 :: k)
  | .Omullhu, [a1, a2] => do
      let rd ← iregOf res
      let rs1 ← iregOf a1
      let rs2 ← iregOf a2
      pure (.Pmulhul rd rs1 rs2 :: k)
  | .Odivl, [a1, a2] => do
      let rd ← iregOf res
      let rs1 ← iregOf a1
      let rs2 ← iregOf a2
      pure (.Pdivl rd rs1 rs2 :: k)
  | .Odivlu, [a1, a2] => do
      let rd ← iregOf res
      let rs1 ← iregOf a1
      let rs2 ← iregOf a2
      pure (.Pdivul rd rs1 rs2 :: k)
  | .Omodl, [a1, a2] => do
      let rd ← iregOf res
      let rs1 ← iregOf a1
      let rs2 ← iregOf a2
      pure (.Preml rd rs1 rs2 :: k)
  | .Omodlu, [a1, a2] => do
      let rd ← iregOf res
      let rs1 ← iregOf a1
      let rs2 ← iregOf a2
      pure (.Premul rd rs1 rs2 :: k)
  | .Oandl, [a1, a2] => do
      let rd ← iregOf res
      let rs1 ← iregOf a1
      let rs2 ← iregOf a2
      pure (.Pandl rd rs1 rs2 :: k)
  | .Oandlimm n, [a1] => do
      let rd ← iregOf res
      let rs ← iregOf a1
      pure (andimm64 rd rs n k)
  | .Oorl, [a1, a2] => do
      let rd ← iregOf res
      let rs1 ← iregOf a1
      let rs2 ← iregOf a2
      pure (.Porl rd rs1 rs2 :: k)
  | .Oorlimm n, [a1] => do
      let rd ← iregOf res
      let rs ← iregOf a1
      pure (orimm64 rd rs n k)
  | .Oxorl, [a1, a2] => do
      let rd ← iregOf res
      let rs1 ← iregOf a1
      let rs2 ← iregOf a2
      pure (.Pxorl rd rs1 rs2 :: k)
  | .Oxorlimm n, [a1] => do
      let rd ← iregOf res
      let rs ← iregOf a1
      pure (xorimm64 rd rs n k)
  | .Oshll, [a1, a2] => do
      let rd ← iregOf res
      let rs1 ← iregOf a1
      let rs2 ← iregOf a2
      pure (.Pslll rd rs1 rs2 :: k)
  | .Oshllimm n, [a1] => do
      let rd ← iregOf res
      let rs ← iregOf a1
      pure (.Psllil rd rs n :: k)
  | .Oshrl, [a1, a2] => do
      let rd ← iregOf res
      let rs1 ← iregOf a1
      let rs2 ← iregOf a2
      pure (.Psral rd rs1 rs2 :: k)
  | .Oshrlimm n, [a1] => do
      let rd ← iregOf res
      let rs ← iregOf a1
      pure (.Psrail rd rs n :: k)
  | .Oshrlu, [a1, a2] => do
      let rd ← iregOf res
      let rs1 ← iregOf a1
      let rs2 ← iregOf a2
      pure (.Psrll rd rs1 rs2 :: k)
  | .Oshrluimm n, [a1] => do
      let rd ← iregOf res
      let rs ← iregOf a1
      pure (.Psrlil rd rs n :: k)
  | .Onegf, [a1] => do
      let rd ← fregOf res
      let rs ← fregOf a1
      pure (.Pfnegd rd rs :: k)
  | .Oabsf, [a1] => do
      let rd ← fregOf res
      let rs ← fregOf a1
      pure (.Pfabsd rd rs :: k)
  | .Oaddf, [a1, a2] => do
      let rd ← fregOf res
      let rs1 ← fregOf a1
      let rs2 ← fregOf a2
      pure (.Pfaddd rd rs1 rs2 :: k)
  | .Osubf, [a1, a2] => do
      let rd ← fregOf res
      let rs1 ← fregOf a1
      let rs2 ← fregOf a2
      pure (.Pfsubd rd rs1 rs2 :: k)
  | .Omulf, [a1, a2] => do
      let rd ← fregOf res
      let rs1 ← fregOf a1
      let rs2 ← fregOf a2
      pure (.Pfmuld rd rs1 rs2 :: k)
  | .Odivf, [a1, a2] => do
      let rd ← fregOf res
      let rs1 ← fregOf a1
      let rs2 ← fregOf a2
      pure (.Pfdivd rd rs1 rs2 :: k)
  | .Onegfs, [a1] => do
      let rd ← fregOf res
      let rs ← fregOf a1
      pure (.Pfnegs rd rs :: k)
  | .Oabsfs, [a1] => do
      let rd ← fregOf res
      let rs ← fregOf a1
      pure (.Pfabss rd rs :: k)
  | .Oaddfs, [a1, a2] => do
      let rd ← fregOf res
      let rs1 ← fregOf a1
      let rs2 ← fregOf a2
      pure (.Pfadds rd rs1 rs2 :: k)
  | .Osubfs, [a1, a2] => do
      let rd ← fregOf res
      let rs1 ← fregOf a1
      let rs2 ← fregOf a2
      pure (.Pfsubs rd rs1 rs2 :: k)
  | .Omulfs, [a1, a2] => do
      let rd ← fregOf res
      let rs1 ← fregOf a1
      let rs2 ← fregOf a2
      pure (.Pfmuls rd rs1 rs2 :: k)
  | .Odivfs, [a1, a2] => do
      let rd ← fregOf res
      let rs1 ← fregOf a1
      let rs2 ← fregOf a2
      pure (.Pfdivs rd rs1 rs2 :: k)
  | .Osingleoffloat, [a1] => do
      let rd ← fregOf res
      let rs ← fregOf a1
      pure (.Pfcvtsd rd rs :: k)
  | .Ofloatofsingle, [a1] => do
      let rd ← fregOf res
      let rs ← fregOf a1
      pure (.Pfcvtds rd rs :: k)
  | .Ointoffloat, [a1] => do
      let rd ← iregOf res
      let rs ← fregOf a1
      pure (.Pfcvtwd rd rs :: k)
  | .Ointuoffloat, [a1] => do
      let rd ← iregOf res
      let rs ← fregOf a1
      pure (.Pfcvtwud rd rs :: k)
  | .Ofloatofint, [a1] => do
      let rd ← fregOf res
      let rs ← iregOf a1
      pure (.Pfcvtdw rd rs :: k)
  | .Ofloatofintu, [a1] => do
      let rd ← fregOf res
      let rs ← iregOf a1
      pure (.Pfcvtdwu rd rs :: k)
  | .Ointofsingle, [a1] => do
      let rd ← iregOf res
      let rs ← fregOf a1
      pure (.Pfcvtws rd rs :: k)
  | .Ointuofsingle, [a1] => do
      let rd ← iregOf res
      let rs ← fregOf a1
      pure (.Pfcvtwus rd rs :: k)
  | .Osingleofint, [a1] => do
      let rd ← fregOf res
      let rs ← iregOf a1
      pure (.Pfcvtsw rd rs :: k)
  | .Osingleofintu, [a1] => do
      let rd ← fregOf res
      let rs ← iregOf a1
      pure (.Pfcvtswu rd rs :: k)
  | .Olongoffloat, [a1] => do
      let rd ← iregOf res
      let rs ← fregOf a1
      pure (.Pfcvtld rd rs :: k)
  | .Olonguoffloat, [a1] => do
      let rd ← iregOf res
      let rs ← fregOf a1
      pure (.Pfcvtlud rd rs :: k)
  | .Ofloatoflong, [a1] => do
      let rd ← fregOf res
      let rs ← iregOf a1
      pure (.Pfcvtdl rd rs :: k)
  | .Ofloatoflongu, [a1] => do
      let rd ← fregOf res
      let rs ← iregOf a1
      pure (.Pfcvtdlu rd rs :: k)
  | .Olongofsingle, [a1] => do
      let rd ← iregOf res
      let rs ← fregOf a1
      pure (.Pfcvtls rd rs :: k)
  | .Olonguofsingle, [a1] => do
      let rd ← iregOf res
      let rs ← fregOf a1
      pure (.Pfcvtlus rd rs :: k)
  | .Osingleoflong, [a1] => do
      let rd ← fregOf res
      let rs ← iregOf a1
      pure (.Pfcvtsl rd rs :: k)
  | .Osingleoflongu, [a1] => do
      let rd ← fregOf res
      let rs ← iregOf a1
      pure (.Pfcvtslu rd rs :: k)
  | _, _ => .Error "Asmgen.transl_op"

/-! ## Accessing data in the stack frame -/

/-- `Asmgen.indexed_memory_access` -/
def indexedMemoryAccess (mkInstr : Ireg → Offset → Instruction) (base : Ireg)
    (ofs : Integers.Ptrofs) (k : Code) : Code :=
  if Archi.ptr64 then
    match makeImmed64 (Integers.Ptrofs.to_int64 ofs) with
    | .Imm64_single imm => mkInstr base (.Ofsimm (Integers.Ptrofs.of_int64 imm)) :: k
    | .Imm64_pair hi lo =>
        .Pluil Ireg.X31 hi :: .Paddl Ireg.X31 base Ireg.X31 ::
          mkInstr Ireg.X31 (.Ofsimm (Integers.Ptrofs.of_int64 lo)) :: k
    | .Imm64_large imm =>
        .Ploadli Ireg.X31 imm :: .Paddl Ireg.X31 base Ireg.X31 ::
          mkInstr Ireg.X31 (.Ofsimm Integers.Ptrofs.zero) :: k
  else
    match makeImmed32 (Integers.Ptrofs.to_int ofs) with
    | .Imm32_single imm => mkInstr base (.Ofsimm (Integers.Ptrofs.of_int imm)) :: k
    | .Imm32_pair hi lo =>
        .Pluiw Ireg.X31 hi :: .Paddw Ireg.X31 base Ireg.X31 ::
          mkInstr Ireg.X31 (.Ofsimm (Integers.Ptrofs.of_int lo)) :: k

/-- `Asmgen.loadind` -/
def loadind (base : Ireg) (ofs : Integers.Ptrofs) (ty : ATyp) (dst : Mreg) (k : Code) :
    Res Code :=
  match ty, pregOf dst with
  | .Tint, .IR rd => .OK (indexedMemoryAccess (.Plw rd) base ofs k)
  | .Tlong, .IR rd => .OK (indexedMemoryAccess (.Pld rd) base ofs k)
  | .Tsingle, .FR rd => .OK (indexedMemoryAccess (.Pfls rd) base ofs k)
  | .Tfloat, .FR rd => .OK (indexedMemoryAccess (.Pfld rd) base ofs k)
  | .Tany32, .IR rd => .OK (indexedMemoryAccess (.Plw_a rd) base ofs k)
  | .Tany64, .IR rd => .OK (indexedMemoryAccess (.Pld_a rd) base ofs k)
  | .Tany64, .FR rd => .OK (indexedMemoryAccess (.Pfld_a rd) base ofs k)
  | _, _ => .Error "Asmgen.loadind"

/-- `Asmgen.storeind` -/
def storeind (src : Mreg) (base : Ireg) (ofs : Integers.Ptrofs) (ty : ATyp) (k : Code) :
    Res Code :=
  match ty, pregOf src with
  | .Tint, .IR rd => .OK (indexedMemoryAccess (.Psw rd) base ofs k)
  | .Tlong, .IR rd => .OK (indexedMemoryAccess (.Psd rd) base ofs k)
  | .Tsingle, .FR rd => .OK (indexedMemoryAccess (.Pfss rd) base ofs k)
  | .Tfloat, .FR rd => .OK (indexedMemoryAccess (.Pfsd rd) base ofs k)
  | .Tany32, .IR rd => .OK (indexedMemoryAccess (.Psw_a rd) base ofs k)
  | .Tany64, .IR rd => .OK (indexedMemoryAccess (.Psd_a rd) base ofs k)
  | .Tany64, .FR rd => .OK (indexedMemoryAccess (.Pfsd_a rd) base ofs k)
  | _, _ => .Error "Asmgen.storeind"

/-- `Asmgen.loadind_ptr` -/
def loadindPtr (base : Ireg) (ofs : Integers.Ptrofs) (dst : Ireg) (k : Code) : Code :=
  indexedMemoryAccess (if Archi.ptr64 then .Pld dst else .Plw dst) base ofs k

/-- `Asmgen.storeind_ptr` -/
def storeindPtr (src : Ireg) (base : Ireg) (ofs : Integers.Ptrofs) (k : Code) : Code :=
  indexedMemoryAccess (if Archi.ptr64 then .Psd src else .Psw src) base ofs k

/-! ## Loads and stores -/

/-- `Asmgen.transl_memory_access` -/
def translMemoryAccess (mkInstr : Ireg → Offset → Instruction) (addr : Addressing)
    (args : List Mreg) (k : Code) : Res Code :=
  match addr, args with
  | .Aindexed ofs, [a1] => do
      let rs ← iregOf a1
      pure (indexedMemoryAccess mkInstr rs ofs k)
  | .Aglobal id ofs, [] =>
      .OK (.Ploadsymbol_high Ireg.X31 id ofs :: mkInstr Ireg.X31 (.Ofslow id ofs) :: k)
  | .Ainstack ofs, [] => .OK (indexedMemoryAccess mkInstr SP ofs k)
  | _, _ => .Error "Asmgen.transl_memory_access"

/-- `Asmgen.transl_load` -/
def translLoad (chunk : Chunk) (addr : Addressing) (args : List Mreg) (dst : Mreg) (k : Code) :
    Res Code :=
  match chunk with
  | .Mint8signed => do let r ← iregOf dst; translMemoryAccess (.Plb r) addr args k
  | .Mint8unsigned => do let r ← iregOf dst; translMemoryAccess (.Plbu r) addr args k
  | .Mint16signed => do let r ← iregOf dst; translMemoryAccess (.Plh r) addr args k
  | .Mint16unsigned => do let r ← iregOf dst; translMemoryAccess (.Plhu r) addr args k
  | .Mint32 => do let r ← iregOf dst; translMemoryAccess (.Plw r) addr args k
  | .Mint64 => do let r ← iregOf dst; translMemoryAccess (.Pld r) addr args k
  | .Mfloat32 => do let r ← fregOf dst; translMemoryAccess (.Pfls r) addr args k
  | .Mfloat64 => do let r ← fregOf dst; translMemoryAccess (.Pfld r) addr args k
  | _ => .Error "Asmgen.transl_load"

/-- `Asmgen.transl_store` -/
def translStore (chunk : Chunk) (addr : Addressing) (args : List Mreg) (src : Mreg) (k : Code) :
    Res Code :=
  match chunk with
  | .Mint8unsigned => do let r ← iregOf src; translMemoryAccess (.Psb r) addr args k
  | .Mint16unsigned => do let r ← iregOf src; translMemoryAccess (.Psh r) addr args k
  | .Mint32 => do let r ← iregOf src; translMemoryAccess (.Psw r) addr args k
  | .Mint64 => do let r ← iregOf src; translMemoryAccess (.Psd r) addr args k
  | .Mfloat32 => do let r ← fregOf src; translMemoryAccess (.Pfss r) addr args k
  | .Mfloat64 => do let r ← fregOf src; translMemoryAccess (.Pfsd r) addr args k
  | _ => .Error "Asmgen.transl_store"

/-! ## Instructions, code, functions, programs -/

/-- `Asmgen.make_epilogue` -/
def makeEpilogue (f : Mach.Function) (k : Code) : Code :=
  loadindPtr SP f.fn_retaddr_ofs RA (.Pfreeframe f.fn_stacksize f.fn_link_ofs :: k)

/-- `Asmgen.transl_instr`.  `ep`: does `X30` hold the parent's stack
pointer? -/
def translInstr (o : Options) (f : Mach.Function) (i : Mach.Instruction) (ep : Bool) (k : Code) :
    Res Code :=
  match i with
  | .Mgetstack ofs ty dst => loadind SP ofs ty dst k
  | .Msetstack src ofs ty => storeind src SP ofs ty k
  | .Mgetparam ofs ty dst => do
      let c ← loadind .X30 ofs ty dst k
      pure (if ep then c else loadindPtr SP f.fn_link_ofs .X30 c)
  | .Mop op args res => translOp o op args res k
  | .Mload chunk addr args dst => translLoad chunk addr args dst k
  | .Mstore chunk addr args src => translStore chunk addr args src k
  | .Mcall sig (.inl r) => do let r1 ← iregOf r; pure (.Pjal_r r1 sig :: k)
  | .Mcall sig (.inr symb) => .OK (.Pjal_s symb sig :: k)
  | .Mtailcall sig (.inl r) => do
      let r1 ← iregOf r
      pure (makeEpilogue f (.Pj_r r1 sig :: k))
  | .Mtailcall sig (.inr symb) => .OK (makeEpilogue f (.Pj_s symb sig :: k))
  | .Mbuiltin ef args res =>
      .OK (.Pbuiltin ef (args.map (BuiltinArg.map pregOf)) (BuiltinRes.map pregOf res) :: k)
  | .Mlabel lbl => .OK (.Plabel lbl :: k)
  | .Mgoto lbl => .OK (.Pj_l lbl :: k)
  | .Mcond cond args lbl => translCbranch cond args lbl k
  | .Mjumptable arg tbl => do let r ← iregOf arg; pure (.Pbtbl r tbl :: k)
  | .Mreturn => .OK (makeEpilogue f (.Pj_r RA f.fn_sig :: k))

/-- `Asmgen.it1_is_parent` -/
def it1IsParent (before : Bool) (i : Mach.Instruction) : Bool :=
  match i with
  | .Msetstack .. => before
  | .Mgetparam _ _ dst => !(decide (dst = .R30))
  | .Mop _ _ res => before && !(decide (res = .R30))
  | _ => false

/-- `Asmgen.transl_code`: the naive (non-tail-recursive) translation, kept
as specification. -/
def translCode (o : Options) (f : Mach.Function) : List Mach.Instruction → Bool → Res Code
  | [], _ => .OK []
  | i1 :: il', it1p => do
      let k ← translCode o f il' (it1IsParent it1p i1)
      translInstr o f i1 it1p k

/-- `Asmgen.transl_code_rec`: the same in continuation-passing style. -/
def translCodeRec (o : Options) (f : Mach.Function) :
    List Mach.Instruction → Bool → (Code → Res Code) → Res Code
  | [], _, k => k []
  | i1 :: il', it1p, k =>
      translCodeRec o f il' (it1IsParent it1p i1)
        (fun c1 => do let c2 ← translInstr o f i1 it1p c1; k c2)

/-- `Asmgen.transl_code'` -/
def translCode' (o : Options) (f : Mach.Function) (il : List Mach.Instruction) (it1p : Bool) :
    Res Code :=
  translCodeRec o f il it1p (fun c => .OK c)

/-- `Asmgen.transl_function` -/
def translFunction (o : Options) (f : Mach.Function) : Res Asm.Function := do
  let c ← translCode' o f f.fn_code true
  pure { fn_sig := f.fn_sig,
         fn_code := .Pallocframe f.fn_stacksize f.fn_link_ofs ::
           storeindPtr RA SP f.fn_retaddr_ofs
             (.Pcfi_rel_offset (Integers.Ptrofs.to_int f.fn_retaddr_ofs) :: c) }

/-- `Asmgen.transf_function`: also checks that the code has fewer than
`2^64` instructions, so that the offset part of `PC` cannot wrap around. -/
def transfFunction (o : Options) (f : Mach.Function) : Res Asm.Function := do
  let tf ← translFunction o f
  if Integers.Ptrofs.max_unsigned < (tf.fn_code.length : Z) then .Error "code size exceeded"
  else pure tf

/-- `Asmgen.transf_fundef` -/
def transfFundef (o : Options) (f : Mach.Fundef) : Res Asm.Fundef :=
  ASTFundef.transfPartial (transfFunction o) f

/-- `Asmgen.transf_program` -/
def transfProgram (o : Options) (p : Mach.Program) : Res Asm.Program :=
  transformPartialProgram (transfFundef o) p

/-! ## Equivalence of the two code translations (`Asmgenproof.v`) -/

private theorem translCodeRec_spec (o : Options) (f : Mach.Function) :
    ∀ (il : List Mach.Instruction) (it1p : Bool) (k : Code → Res Code),
      translCodeRec o f il it1p k = Res.bind (translCode o f il it1p) k
  | [], _, k => rfl
  | i1 :: il', it1p, k => by
      rw [translCodeRec, translCodeRec_spec o f il']
      simp only [translCode]
      show _ = Res.bind (Res.bind _ _) _
      cases translCode o f il' (it1IsParent it1p i1) with
      | OK a => rfl
      | Error m => rfl

/-- `Asmgenproof.transl_code'_transl_code` -/
theorem transl_code'_transl_code (o : Options) (f : Mach.Function) (il : List Mach.Instruction)
    (it1p : Bool) : translCode' o f il it1p = translCode o f il it1p := by
  rw [translCode', translCodeRec_spec]
  cases translCode o f il it1p <;> rfl

end Asmgen
end RiscV
end CC
