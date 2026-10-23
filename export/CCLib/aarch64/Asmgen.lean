/-
  Translation from Mach to AArch64 assembly — port of `aarch64/Asmgen.v`
  (whole file).

  Ported: `ireg_of`, `freg_of`, the logical-immediate automaton
  (`Automaton.state`, `next`, `accepting`, `run`), `logical_imm_length`,
  `is_logical_imm32/64`, `is_arith_imm32/64`, `decompose_int`,
  `negate_decomposition`, `loadimm_k/z/n`, `loadimm`, `loadimm32/64`,
  `addimm_aux`, `addimm32/64`, `logicalimm32/64`, `transl_extension`,
  `move_extended_base`, `move_extended`, `arith_extended`, `shrx32/64`,
  `loadsymbol`, `transl_shift`, `transl_cond`, `cond_for_*`,
  `transl_cond_branch_default`, `transl_cond_branch`, `transl_op`,
  `offset_representable`, `transl_addressing`, `transl_load`,
  `transl_store`, `indexed_memory_access`, `loadind`, `storeind`,
  `loadptr`, `storeptr`, `make_epilogue`, `transl_instr`, `it1_is_parent`,
  `transl_code`, `transl_code_rec`, `transl_code'`, `transl_function`,
  `transf_function`, `transf_fundef`, `transf_program`.
  Also proved: `transl_code'_transl_code` (from `Asmgenproof.v`): the
  continuation-passing translation computes the same result as the naive
  one.

  Differences from Rocq:
  * The OCaml parameters `Asmgen.symbol_is_aligned` and
    `SelectOp.symbol_is_relocatable` are fields of an explicit
    `Asmgen.Options` argument (defaults: no symbol is known to be aligned,
    no symbol is relocatable).
  * `Zzero_ext`, `Z.shiftr`, `Z.ldiff`, `Z.lxor`, `Z.lnot` on the integer
    literals are computed arithmetically (`zzeroExt`, `Int.fdiv`, …); they
    agree with the Rocq definitions on the arguments used here.
  * Error messages are plain strings.
-/
import CCLib.aarch64.Asm
import CCLib.backend.Stacking

namespace CC
namespace Asmgen

open Asm

/-- The OCaml parameters used by Asmgen. -/
structure Options where
  /-- `Asmgen.symbol_is_aligned id sz`: the symbol `id` is `sz`-aligned. -/
  symbolIsAligned : Ident → Z → Bool := fun _ _ => false
  /-- `SelectOp.symbol_is_relocatable` -/
  symbolIsRelocatable : Ident → Bool := fun _ => false

/-! ## Arithmetic on `Z` used below (`Zbits`) -/

/-- `Zbits.Zzero_ext n x`: the low `n` bits of `x` (`0` if `n ≤ 0`). -/
def zzeroExt (n x : Z) : Z :=
  if n ≤ 0 then 0 else Int.emod x ((2 : Z) ^ n.toNat)

/-- `Z.shiftr x n` for `n ≥ 0` (floor division by `2^n`). -/
def zshiftr (x n : Z) : Z := Int.fdiv x ((2 : Z) ^ n.toNat)

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

/-! ## Recognition of immediate arguments for logical integer operations -/

namespace Automaton

/-- `Automaton.state` -/
inductive State where
  | SA | SB | SC | SD | SE | SF | SG | Sbad
  deriving DecidableEq, Repr

/-- `Automaton.start` -/
def start : State := .SA

/-- `Automaton.next` -/
def next : State → Bool → State
  | .SA, false => .SB | .SA, true => .SC
  | .SB, false => .SB | .SB, true => .SD
  | .SC, false => .SE | .SC, true => .SC
  | .SD, false => .SF | .SD, true => .SD
  | .SE, false => .SE | .SE, true => .SG
  | .SF, false => .SF | .SF, true => .Sbad
  | .SG, false => .Sbad | .SG, true => .SG
  | .Sbad, _ => .Sbad

/-- `Automaton.accepting` -/
def accepting : State → Bool
  | .Sbad => false
  | _ => true

/-- `Automaton.run` -/
def run : Nat → State → Z → Bool
  | 0, s, _ => accepting s
  | len + 1, s, x => run len (next s (x % 2 != 0)) (Int.fdiv x 2)

end Automaton

/-- `Asmgen.logical_imm_length` -/
def logicalImmLength (x : Z) (sixtyfour : Bool) : Nat :=
  let test (n : Z) : Bool := zzeroExt n x == zzeroExt n (zshiftr x n)
  if sixtyfour && !(test 32) then 64
  else if !(test 16) then 32
  else if !(test 8) then 16
  else if !(test 4) then 8
  else if !(test 2) then 4
  else 2

/-- `Asmgen.is_logical_imm32` -/
def isLogicalImm32 (x : Integers.Int) : Bool :=
  !(Integers.Int.eq x Integers.Int.zero) && !(Integers.Int.eq x Integers.Int.mone) &&
  Automaton.run (logicalImmLength (Integers.Int.unsigned x) false)
    Automaton.start (Integers.Int.unsigned x)

/-- `Asmgen.is_logical_imm64` -/
def isLogicalImm64 (x : Integers.Int64) : Bool :=
  !(Integers.Int64.eq x Integers.Int64.zero) && !(Integers.Int64.eq x Integers.Int64.mone) &&
  Automaton.run (logicalImmLength (Integers.Int64.unsigned x) true)
    Automaton.start (Integers.Int64.unsigned x)

/-- `Asmgen.is_arith_imm32`: 12-bit unsigned, possibly shifted left 12 bits. -/
def isArithImm32 (x : Integers.Int) : Bool :=
  Integers.Int.eq x (Integers.Int.zero_ext 12 x) ||
  Integers.Int.eq x (Integers.Int.shl (Integers.Int.zero_ext 12
    (Integers.Int.shru x (Integers.Int.repr 12))) (Integers.Int.repr 12))

/-- `Asmgen.is_arith_imm64` -/
def isArithImm64 (x : Integers.Int64) : Bool :=
  Integers.Int64.eq x (Integers.Int64.zero_ext 12 x) ||
  Integers.Int64.eq x (Integers.Int64.shl (Integers.Int64.zero_ext 12
    (Integers.Int64.shru x (Integers.Int64.repr 12))) (Integers.Int64.repr 12))

/-! ## Decomposition of integer literals into 16-bit fragments -/

/-- `Asmgen.decompose_int`.  (`Z.ldiff n (Z.shiftl 65535 p)` clears the
    fragment `frag` at position `p`, i.e. subtracts `frag * 2^p`.) -/
def decomposeInt : Nat → Z → Z → List (Z × Z)
  | 0, _, _ => []
  | N + 1, n, p =>
      let frag := zzeroExt 16 (zshiftr n p)
      if frag == 0 then decomposeInt N n (p + 16)
      else (frag, p) :: decomposeInt N (n - frag * (2 : Z) ^ p.toNat) (p + 16)

/-- `Asmgen.negate_decomposition` (`Z.lxor f 65535 = 65535 - f` for
    `0 ≤ f < 2^16`). -/
def negateDecomposition (l : List (Z × Z)) : List (Z × Z) :=
  l.map (fun np => (65535 - np.1, np.2))

/-- `Asmgen.loadimm_k` -/
def loadimmK (sz : Isize) (rd : Ireg) (l : List (Z × Z)) (k : Code) : Code :=
  l.foldr (fun np k => .Pmovk sz rd np.1 np.2 :: k) k

/-- `Asmgen.loadimm_z` -/
def loadimmZ (sz : Isize) (rd : Ireg) (l : List (Z × Z)) (k : Code) : Code :=
  match l with
  | [] => .Pmovz sz rd 0 0 :: k
  | (n1, p1) :: l => .Pmovz sz rd n1 p1 :: loadimmK sz rd l k

/-- `Asmgen.loadimm_n` -/
def loadimmN (sz : Isize) (rd : Ireg) (l : List (Z × Z)) (k : Code) : Code :=
  match l with
  | [] => .Pmovn sz rd 0 0 :: k
  | (n1, p1) :: l => .Pmovn sz rd n1 p1 :: loadimmK sz rd (negateDecomposition l) k

/-- `Asmgen.loadimm` -/
def loadimm (sz : Isize) (rd : Ireg) (n : Z) (k : Code) : Code :=
  let N := match sz with | .W => 2 | .X => 4
  let dz := decomposeInt N n 0
  let dn := decomposeInt N (-n - 1) 0
  if dz.length ≤ dn.length then loadimmZ sz rd dz k else loadimmN sz rd dn k

/-- `Asmgen.loadimm32` -/
def loadimm32 (rd : Ireg) (n : Integers.Int) (k : Code) : Code :=
  if isLogicalImm32 n then .Porrimm .W rd .XZR (Integers.Int.unsigned n) :: k
  else loadimm .W rd (Integers.Int.unsigned n) k

/-- `Asmgen.loadimm64` -/
def loadimm64 (rd : Ireg) (n : Integers.Int64) (k : Code) : Code :=
  if isLogicalImm64 n then .Porrimm .X rd .XZR (Integers.Int64.unsigned n) :: k
  else loadimm .X rd (Integers.Int64.unsigned n) k

/-! ## Add immediate -/

/-- `Asmgen.addimm_aux` -/
def addimmAux (insn : Iregsp → Iregsp → Z → Instruction) (rd r1 : Iregsp) (n : Z)
    (k : Code) : Code :=
  let nlo := zzeroExt 12 n
  let nhi := n - nlo
  if nhi == 0 then insn rd r1 nlo :: k
  else if nlo == 0 then insn rd r1 nhi :: k
  else insn rd r1 nhi :: insn rd rd nlo :: k

/-- `Asmgen.addimm32` -/
def addimm32 (rd r1 : Ireg) (n : Integers.Int) (k : Code) : Code :=
  let m := Integers.Int.neg n
  if Integers.Int.eq n (Integers.Int.zero_ext 24 n) then
    addimmAux (.Paddimm .W) rd r1 (Integers.Int.unsigned n) k
  else if Integers.Int.eq m (Integers.Int.zero_ext 24 m) then
    addimmAux (.Psubimm .W) rd r1 (Integers.Int.unsigned m) k
  else if Integers.Int.lt n Integers.Int.zero then
    loadimm32 .X16 m (.Psub .W rd r1 .X16 .SOnone :: k)
  else
    loadimm32 .X16 n (.Padd .W rd r1 .X16 .SOnone :: k)

/-- `Asmgen.addimm64` -/
def addimm64 (rd r1 : Iregsp) (n : Integers.Int64) (k : Code) : Code :=
  let m := Integers.Int64.neg n
  if Integers.Int64.eq n (Integers.Int64.zero_ext 24 n) then
    addimmAux (.Paddimm .X) rd r1 (Integers.Int64.unsigned n) k
  else if Integers.Int64.eq m (Integers.Int64.zero_ext 24 m) then
    addimmAux (.Psubimm .X) rd r1 (Integers.Int64.unsigned m) k
  else if Integers.Int64.lt n Integers.Int64.zero then
    loadimm64 .X16 m (.Psubext rd r1 .X16 (.EOuxtx Integers.Int.zero) :: k)
  else
    loadimm64 .X16 n (.Paddext rd r1 .X16 (.EOuxtx Integers.Int.zero) :: k)

/-! ## Logical immediate -/

/-- `Asmgen.logicalimm32` -/
def logicalimm32 (insn1 : Ireg → Ireg0 → Z → Instruction)
    (insn2 : Ireg → Ireg0 → Ireg → ShiftOp → Instruction)
    (rd r1 : Ireg) (n : Integers.Int) (k : Code) : Code :=
  if isLogicalImm32 n then insn1 rd r1 (Integers.Int.unsigned n) :: k
  else loadimm32 .X16 n (insn2 rd r1 .X16 .SOnone :: k)

/-- `Asmgen.logicalimm64` -/
def logicalimm64 (insn1 : Ireg → Ireg0 → Z → Instruction)
    (insn2 : Ireg → Ireg0 → Ireg → ShiftOp → Instruction)
    (rd r1 : Ireg) (n : Integers.Int64) (k : Code) : Code :=
  if isLogicalImm64 n then insn1 rd r1 (Integers.Int64.unsigned n) :: k
  else loadimm64 .X16 n (insn2 rd r1 .X16 .SOnone :: k)

/-! ## Sign- or zero-extended arithmetic -/

/-- `Asmgen.transl_extension` -/
def translExtension (ex : Op.Extension) (a : Integers.Int) : ExtendOp :=
  match ex with
  | .Xsgn32 => .EOsxtw a
  | .Xuns32 => .EOuxtw a

/-- `Asmgen.move_extended_base` -/
def moveExtendedBase (rd r1 : Ireg) (ex : Op.Extension) (k : Code) : Code :=
  match ex with
  | .Xsgn32 => .Pcvtsw2x rd r1 :: k
  | .Xuns32 => .Pcvtuw2x rd r1 :: k

/-- `Asmgen.move_extended` -/
def moveExtended (rd r1 : Ireg) (ex : Op.Extension) (a : Integers.Int) (k : Code) : Code :=
  if Integers.Int.eq a Integers.Int.zero then moveExtendedBase rd r1 ex k
  else moveExtendedBase rd r1 ex (.Padd .X rd .XZR rd (.SOlsl a) :: k)

/-- `Asmgen.arith_extended` -/
def arithExtended (insnX : Iregsp → Iregsp → Ireg → ExtendOp → Instruction)
    (insnS : Ireg → Ireg0 → Ireg → ShiftOp → Instruction)
    (rd r1 r2 : Ireg) (ex : Op.Extension) (a : Integers.Int) (k : Code) : Code :=
  if Integers.Int.ltu a (Integers.Int.repr 5) then
    insnX rd r1 r2 (translExtension ex a) :: k
  else
    moveExtendedBase .X16 r2 ex (insnS rd r1 .X16 (.SOlsl a) :: k)

/-! ## Extended right shift -/

/-- `Asmgen.shrx32` -/
def shrx32 (rd r1 : Ireg) (n : Integers.Int) (k : Code) : Code :=
  if Integers.Int.eq n Integers.Int.zero then .Pmov rd r1 :: k
  else
    .Porr .W .X16 .XZR r1 (.SOasr (Integers.Int.repr 31)) ::
    .Padd .W .X16 r1 .X16 (.SOlsr (Integers.Int.sub Integers.Int.iwordsize n)) ::
    .Porr .W rd .XZR .X16 (.SOasr n) :: k

/-- `Asmgen.shrx64` -/
def shrx64 (rd r1 : Ireg) (n : Integers.Int) (k : Code) : Code :=
  if Integers.Int.eq n Integers.Int.zero then .Pmov rd r1 :: k
  else
    .Porr .X .X16 .XZR r1 (.SOasr (Integers.Int.repr 63)) ::
    .Padd .X .X16 r1 .X16 (.SOlsr (Integers.Int.sub Integers.Int64.iwordsize' n)) ::
    .Porr .X rd .XZR .X16 (.SOasr n) :: k

/-! ## Symbols, shifts -/

/-- `Asmgen.loadsymbol`: load the address `id + ofs` in `rd`. -/
def loadsymbol (o : Options) (rd : Ireg) (id : Ident) (ofs : Integers.Ptrofs) (k : Code) :
    Code :=
  if o.symbolIsRelocatable id then
    if Integers.Ptrofs.eq ofs Integers.Ptrofs.zero then .Ploadsymbol rd id :: k
    else .Ploadsymbol rd id :: addimm64 rd rd (Integers.Ptrofs.to_int64 ofs) k
  else .Padrp rd id ofs :: .Paddadr rd rd id ofs :: k

/-- `Asmgen.transl_shift` -/
def translShift (s : Op.Shift) (a : Integers.Int) : ShiftOp :=
  match s with
  | .Slsl => .SOlsl a
  | .Slsr => .SOlsr a
  | .Sasr => .SOasr a
  | .Sror => .SOror a

/-! ## Conditions -/

/-- `Asmgen.transl_cond` -/
def translCond (cond : Op.Condition) (args : List Mreg) (k : Code) : Res Code :=
  match cond, args with
  | .Ccomp _, [a1, a2] | .Ccompu _, [a1, a2] => do
      let r1 ← iregOf a1; let r2 ← iregOf a2
      pure (.Pcmp .W r1 r2 .SOnone :: k)
  | .Ccompshift _ s a, [a1, a2] | .Ccompushift _ s a, [a1, a2] => do
      let r1 ← iregOf a1; let r2 ← iregOf a2
      pure (.Pcmp .W r1 r2 (translShift s a.a32_amount) :: k)
  | .Ccompimm _ n, [a1] | .Ccompuimm _ n, [a1] => do
      let r1 ← iregOf a1
      pure (if isArithImm32 n then .Pcmpimm .W r1 (Integers.Int.unsigned n) :: k
        else if isArithImm32 (Integers.Int.neg n) then
          .Pcmnimm .W r1 (Integers.Int.unsigned (Integers.Int.neg n)) :: k
        else loadimm32 .X16 n (.Pcmp .W r1 .X16 .SOnone :: k))
  | .Cmaskzero n, [a1] | .Cmasknotzero n, [a1] => do
      let r1 ← iregOf a1
      pure (if isLogicalImm32 n then .Ptstimm .W r1 (Integers.Int.unsigned n) :: k
        else loadimm32 .X16 n (.Ptst .W r1 .X16 .SOnone :: k))
  | .Ccompl _, [a1, a2] | .Ccomplu _, [a1, a2] => do
      let r1 ← iregOf a1; let r2 ← iregOf a2
      pure (.Pcmp .X r1 r2 .SOnone :: k)
  | .Ccomplshift _ s a, [a1, a2] | .Ccomplushift _ s a, [a1, a2] => do
      let r1 ← iregOf a1; let r2 ← iregOf a2
      pure (.Pcmp .X r1 r2 (translShift s a.a64_amount) :: k)
  | .Ccomplimm _ n, [a1] | .Ccompluimm _ n, [a1] => do
      let r1 ← iregOf a1
      pure (if isArithImm64 n then .Pcmpimm .X r1 (Integers.Int64.unsigned n) :: k
        else if isArithImm64 (Integers.Int64.neg n) then
          .Pcmnimm .X r1 (Integers.Int64.unsigned (Integers.Int64.neg n)) :: k
        else loadimm64 .X16 n (.Pcmp .X r1 .X16 .SOnone :: k))
  | .Cmasklzero n, [a1] | .Cmasklnotzero n, [a1] => do
      let r1 ← iregOf a1
      pure (if isLogicalImm64 n then .Ptstimm .X r1 (Integers.Int64.unsigned n) :: k
        else loadimm64 .X16 n (.Ptst .X r1 .X16 .SOnone :: k))
  | .Ccompf _, [a1, a2] | .Cnotcompf _, [a1, a2] => do
      let r1 ← fregOf a1; let r2 ← fregOf a2
      pure (.Pfcmp .D r1 r2 :: k)
  | .Ccompfzero _, [a1] | .Cnotcompfzero _, [a1] => do
      let r1 ← fregOf a1
      pure (.Pfcmp0 .D r1 :: k)
  | .Ccompfs _, [a1, a2] | .Cnotcompfs _, [a1, a2] => do
      let r1 ← fregOf a1; let r2 ← fregOf a2
      pure (.Pfcmp .S r1 r2 :: k)
  | .Ccompfszero _, [a1] | .Cnotcompfszero _, [a1] => do
      let r1 ← fregOf a1
      pure (.Pfcmp0 .S r1 :: k)
  | _, _ => .Error "Asmgen.transl_cond"

/-- `Asmgen.cond_for_signed_cmp` -/
def condForSignedCmp : Comparison → Testcond
  | .Ceq => .TCeq | .Cne => .TCne | .Clt => .TClt
  | .Cle => .TCle | .Cgt => .TCgt | .Cge => .TCge

/-- `Asmgen.cond_for_unsigned_cmp` -/
def condForUnsignedCmp : Comparison → Testcond
  | .Ceq => .TCeq | .Cne => .TCne | .Clt => .TClo
  | .Cle => .TCls | .Cgt => .TChi | .Cge => .TChs

/-- `Asmgen.cond_for_float_cmp` -/
def condForFloatCmp : Comparison → Testcond
  | .Ceq => .TCeq | .Cne => .TCne | .Clt => .TCmi
  | .Cle => .TCls | .Cgt => .TCgt | .Cge => .TCge

/-- `Asmgen.cond_for_float_not_cmp` -/
def condForFloatNotCmp : Comparison → Testcond
  | .Ceq => .TCne | .Cne => .TCeq | .Clt => .TCpl
  | .Cle => .TChi | .Cgt => .TCle | .Cge => .TClt

/-- `Asmgen.cond_for_cond` -/
def condForCond : Op.Condition → Testcond
  | .Ccomp c => condForSignedCmp c
  | .Ccompu c => condForUnsignedCmp c
  | .Ccompshift c _ _ => condForSignedCmp c
  | .Ccompushift c _ _ => condForUnsignedCmp c
  | .Ccompimm c _ => condForSignedCmp c
  | .Ccompuimm c _ => condForUnsignedCmp c
  | .Cmaskzero _ => .TCeq
  | .Cmasknotzero _ => .TCne
  | .Ccompl c => condForSignedCmp c
  | .Ccomplu c => condForUnsignedCmp c
  | .Ccomplshift c _ _ => condForSignedCmp c
  | .Ccomplushift c _ _ => condForUnsignedCmp c
  | .Ccomplimm c _ => condForSignedCmp c
  | .Ccompluimm c _ => condForUnsignedCmp c
  | .Cmasklzero _ => .TCeq
  | .Cmasklnotzero _ => .TCne
  | .Ccompf c => condForFloatCmp c
  | .Cnotcompf c => condForFloatNotCmp c
  | .Ccompfzero c => condForFloatCmp c
  | .Cnotcompfzero c => condForFloatNotCmp c
  | .Ccompfs c => condForFloatCmp c
  | .Cnotcompfs c => condForFloatNotCmp c
  | .Ccompfszero c => condForFloatCmp c
  | .Cnotcompfszero c => condForFloatNotCmp c

/-- `Asmgen.transl_cond_branch_default` -/
def translCondBranchDefault (c : Op.Condition) (args : List Mreg) (lbl : Label) (k : Code) :
    Res Code :=
  translCond c args (.Pbc (condForCond c) lbl :: k)

/-- `Asmgen.transl_cond_branch`: conditional branches that can be
    implemented without setting and testing the condition flags. -/
def translCondBranch (c : Op.Condition) (args : List Mreg) (lbl : Label) (k : Code) :
    Res Code :=
  match args, c with
  | [a1], .Ccompimm .Cne n | [a1], .Ccompuimm .Cne n =>
      if Integers.Int.eq n Integers.Int.zero then do
        let r1 ← iregOf a1; pure (.Pcbnz .W r1 lbl :: k)
      else translCondBranchDefault c args lbl k
  | [a1], .Ccompimm .Ceq n | [a1], .Ccompuimm .Ceq n =>
      if Integers.Int.eq n Integers.Int.zero then do
        let r1 ← iregOf a1; pure (.Pcbz .W r1 lbl :: k)
      else translCondBranchDefault c args lbl k
  | [a1], .Ccomplimm .Cne n | [a1], .Ccompluimm .Cne n =>
      if Integers.Int64.eq n Integers.Int64.zero then do
        let r1 ← iregOf a1; pure (.Pcbnz .X r1 lbl :: k)
      else translCondBranchDefault c args lbl k
  | [a1], .Ccomplimm .Ceq n | [a1], .Ccompluimm .Ceq n =>
      if Integers.Int64.eq n Integers.Int64.zero then do
        let r1 ← iregOf a1; pure (.Pcbz .X r1 lbl :: k)
      else translCondBranchDefault c args lbl k
  | [a1], .Cmaskzero n =>
      match Integers.Int.is_power2 n with
      | some bit => do let r1 ← iregOf a1; pure (.Ptbz .W r1 bit lbl :: k)
      | none => translCondBranchDefault c args lbl k
  | [a1], .Cmasknotzero n =>
      match Integers.Int.is_power2 n with
      | some bit => do let r1 ← iregOf a1; pure (.Ptbnz .W r1 bit lbl :: k)
      | none => translCondBranchDefault c args lbl k
  | [a1], .Cmasklzero n =>
      match Integers.Int64.is_power2' n with
      | some bit => do let r1 ← iregOf a1; pure (.Ptbz .X r1 bit lbl :: k)
      | none => translCondBranchDefault c args lbl k
  | [a1], .Cmasklnotzero n =>
      match Integers.Int64.is_power2' n with
      | some bit => do let r1 ← iregOf a1; pure (.Ptbnz .X r1 bit lbl :: k)
      | none => translCondBranchDefault c args lbl k
  | _, _ => translCondBranchDefault c args lbl k

/-! ## Arithmetic operations -/

/-- One integer argument and an integer result (`do rd <- ireg_of res;
    do r1 <- ireg_of a1; …`). -/
def ii1 (res a1 : Mreg) (f : Ireg → Ireg → Code) : Res Code := do
  let rd ← iregOf res; let r1 ← iregOf a1; pure (f rd r1)

/-- Two integer arguments and an integer result. -/
def ii2 (res a1 a2 : Mreg) (f : Ireg → Ireg → Ireg → Code) : Res Code := do
  let rd ← iregOf res; let r1 ← iregOf a1; let r2 ← iregOf a2; pure (f rd r1 r2)

/-- Three integer arguments and an integer result. -/
def ii3 (res a1 a2 a3 : Mreg) (f : Ireg → Ireg → Ireg → Ireg → Code) : Res Code := do
  let rd ← iregOf res; let r1 ← iregOf a1; let r2 ← iregOf a2; let r3 ← iregOf a3
  pure (f rd r1 r2 r3)

/-- One float argument and a float result. -/
def ff1 (res a1 : Mreg) (f : Freg → Freg → Code) : Res Code := do
  let rd ← fregOf res; let r1 ← fregOf a1; pure (f rd r1)

/-- Two float arguments and a float result. -/
def ff2 (res a1 a2 : Mreg) (f : Freg → Freg → Freg → Code) : Res Code := do
  let rd ← fregOf res; let r1 ← fregOf a1; let r2 ← fregOf a2; pure (f rd r1 r2)

/-- A float argument and an integer result. -/
def if1 (res a1 : Mreg) (f : Ireg → Freg → Code) : Res Code := do
  let rd ← iregOf res; let r1 ← fregOf a1; pure (f rd r1)

/-- An integer argument and a float result. -/
def fi1 (res a1 : Mreg) (f : Freg → Ireg → Code) : Res Code := do
  let rd ← fregOf res; let r1 ← iregOf a1; pure (f rd r1)

/-- `Asmgen.transl_op`: the instructions computing `res <- op(args)`,
    prepended to `k`. -/
def translOp (o : Options) (op : Op.Operation) (args : List Mreg) (res : Mreg) (k : Code) :
    Res Code :=
  match op, args with
  | .Omove, [a1] =>
      match pregOf res, pregOf a1 with
      | .IR r, .IR a => .OK (.Pmov r a :: k)
      | .FR r, .FR a => .OK (.Pfmov r a :: k)
      | _, _ => .Error "Asmgen.Omove"
  | .Ointconst n, [] => do let rd ← iregOf res; pure (loadimm32 rd n k)
  | .Olongconst n, [] => do let rd ← iregOf res; pure (loadimm64 rd n k)
  | .Ofloatconst f, [] => do
      let rd ← fregOf res
      pure (if f = Floats.Float.zero then .Pfmovi .D rd .XZR :: k else .Pfmovimmd rd f :: k)
  | .Osingleconst f, [] => do
      let rd ← fregOf res
      pure (if f = Floats.Float32.zero then .Pfmovi .S rd .XZR :: k
        else .Pfmovimms rd f :: k)
  | .Oaddrsymbol id ofs, [] => do let rd ← iregOf res; pure (loadsymbol o rd id ofs k)
  | .Oaddrstack ofs, [] => do
      let rd ← iregOf res; pure (addimm64 rd .XSP (Integers.Ptrofs.to_int64 ofs) k)
  -- 32-bit integer arithmetic
  | .Oshift s a, [a1] =>
      ii1 res a1 fun rd r1 => .Porr .W rd .XZR r1 (translShift s a.a32_amount) :: k
  | .Oadd, [a1, a2] => ii2 res a1 a2 fun rd r1 r2 => .Padd .W rd r1 r2 .SOnone :: k
  | .Oaddshift s a, [a1, a2] =>
      ii2 res a1 a2 fun rd r1 r2 => .Padd .W rd r1 r2 (translShift s a.a32_amount) :: k
  | .Oaddimm n, [a1] => ii1 res a1 fun rd r1 => addimm32 rd r1 n k
  | .Oneg, [a1] => ii1 res a1 fun rd r1 => .Psub .W rd .XZR r1 .SOnone :: k
  | .Onegshift s a, [a1] =>
      ii1 res a1 fun rd r1 => .Psub .W rd .XZR r1 (translShift s a.a32_amount) :: k
  | .Osub, [a1, a2] => ii2 res a1 a2 fun rd r1 r2 => .Psub .W rd r1 r2 .SOnone :: k
  | .Osubshift s a, [a1, a2] =>
      ii2 res a1 a2 fun rd r1 r2 => .Psub .W rd r1 r2 (translShift s a.a32_amount) :: k
  | .Omul, [a1, a2] => ii2 res a1 a2 fun rd r1 r2 => .Pmadd .W rd r1 r2 .XZR :: k
  | .Omuladd, [a1, a2, a3] =>
      ii3 res a1 a2 a3 fun rd r1 r2 r3 => .Pmadd .W rd r2 r3 r1 :: k
  | .Omulsub, [a1, a2, a3] =>
      ii3 res a1 a2 a3 fun rd r1 r2 r3 => .Pmsub .W rd r2 r3 r1 :: k
  | .Odiv, [a1, a2] => ii2 res a1 a2 fun rd r1 r2 => .Psdiv .W rd r1 r2 :: k
  | .Odivu, [a1, a2] => ii2 res a1 a2 fun rd r1 r2 => .Pudiv .W rd r1 r2 :: k
  | .Oand, [a1, a2] => ii2 res a1 a2 fun rd r1 r2 => .Pand .W rd r1 r2 .SOnone :: k
  | .Oandshift s a, [a1, a2] =>
      ii2 res a1 a2 fun rd r1 r2 => .Pand .W rd r1 r2 (translShift s a.a32_amount) :: k
  | .Oandimm n, [a1] =>
      ii1 res a1 fun rd r1 => logicalimm32 (.Pandimm .W) (.Pand .W) rd r1 n k
  | .Oor, [a1, a2] => ii2 res a1 a2 fun rd r1 r2 => .Porr .W rd r1 r2 .SOnone :: k
  | .Oorshift s a, [a1, a2] =>
      ii2 res a1 a2 fun rd r1 r2 => .Porr .W rd r1 r2 (translShift s a.a32_amount) :: k
  | .Oorimm n, [a1] =>
      ii1 res a1 fun rd r1 => logicalimm32 (.Porrimm .W) (.Porr .W) rd r1 n k
  | .Oxor, [a1, a2] => ii2 res a1 a2 fun rd r1 r2 => .Peor .W rd r1 r2 .SOnone :: k
  | .Oxorshift s a, [a1, a2] =>
      ii2 res a1 a2 fun rd r1 r2 => .Peor .W rd r1 r2 (translShift s a.a32_amount) :: k
  | .Oxorimm n, [a1] =>
      ii1 res a1 fun rd r1 => logicalimm32 (.Peorimm .W) (.Peor .W) rd r1 n k
  | .Onot, [a1] => ii1 res a1 fun rd r1 => .Porn .W rd .XZR r1 .SOnone :: k
  | .Onotshift s a, [a1] =>
      ii1 res a1 fun rd r1 => .Porn .W rd .XZR r1 (translShift s a.a32_amount) :: k
  | .Obic, [a1, a2] => ii2 res a1 a2 fun rd r1 r2 => .Pbic .W rd r1 r2 .SOnone :: k
  | .Obicshift s a, [a1, a2] =>
      ii2 res a1 a2 fun rd r1 r2 => .Pbic .W rd r1 r2 (translShift s a.a32_amount) :: k
  | .Oorn, [a1, a2] => ii2 res a1 a2 fun rd r1 r2 => .Porn .W rd r1 r2 .SOnone :: k
  | .Oornshift s a, [a1, a2] =>
      ii2 res a1 a2 fun rd r1 r2 => .Porn .W rd r1 r2 (translShift s a.a32_amount) :: k
  | .Oeqv, [a1, a2] => ii2 res a1 a2 fun rd r1 r2 => .Peon .W rd r1 r2 .SOnone :: k
  | .Oeqvshift s a, [a1, a2] =>
      ii2 res a1 a2 fun rd r1 r2 => .Peon .W rd r1 r2 (translShift s a.a32_amount) :: k
  | .Oshl, [a1, a2] => ii2 res a1 a2 fun rd r1 r2 => .Plslv .W rd r1 r2 :: k
  | .Oshr, [a1, a2] => ii2 res a1 a2 fun rd r1 r2 => .Pasrv .W rd r1 r2 :: k
  | .Oshru, [a1, a2] => ii2 res a1 a2 fun rd r1 r2 => .Plsrv .W rd r1 r2 :: k
  | .Oshrximm n, [a1] => ii1 res a1 fun rd r1 => shrx32 rd r1 n k
  | .Ozext s, [a1] => ii1 res a1 fun rd r1 => .Pubfiz .W rd r1 Integers.Int.zero s :: k
  | .Osext s, [a1] => ii1 res a1 fun rd r1 => .Psbfiz .W rd r1 Integers.Int.zero s :: k
  | .Oshlzext s a, [a1] =>
      ii1 res a1 fun rd r1 => .Pubfiz .W rd r1 a.a32_amount
        (min s (Integers.Int.zwordsize - Integers.Int.unsigned a.a32_amount)) :: k
  | .Oshlsext s a, [a1] =>
      ii1 res a1 fun rd r1 => .Psbfiz .W rd r1 a.a32_amount
        (min s (Integers.Int.zwordsize - Integers.Int.unsigned a.a32_amount)) :: k
  | .Ozextshr a s, [a1] =>
      ii1 res a1 fun rd r1 => .Pubfx .W rd r1 a.a32_amount
        (min s (Integers.Int.zwordsize - Integers.Int.unsigned a.a32_amount)) :: k
  | .Osextshr a s, [a1] =>
      ii1 res a1 fun rd r1 => .Psbfx .W rd r1 a.a32_amount
        (min s (Integers.Int.zwordsize - Integers.Int.unsigned a.a32_amount)) :: k
  -- 64-bit integer arithmetic
  | .Oshiftl s a, [a1] =>
      ii1 res a1 fun rd r1 => .Porr .X rd .XZR r1 (translShift s a.a64_amount) :: k
  | .Oextend x a, [a1] => ii1 res a1 fun rd r1 => moveExtended rd r1 x a.a64_amount k
  -- `Omakelong` and `Ohighlong` should not occur
  | .Olowlong, [a1] => do
      let rd ← iregOf res; let r1 ← iregOf a1
      if rd = r1 then pure (.Pcvtx2w rd :: k) else .Error "Assertion failed"
  | .Oaddl, [a1, a2] => ii2 res a1 a2 fun rd r1 r2 => .Padd .X rd r1 r2 .SOnone :: k
  | .Oaddlshift s a, [a1, a2] =>
      ii2 res a1 a2 fun rd r1 r2 => .Padd .X rd r1 r2 (translShift s a.a64_amount) :: k
  | .Oaddlext x a, [a1, a2] =>
      ii2 res a1 a2 fun rd r1 r2 => arithExtended .Paddext (.Padd .X) rd r1 r2 x a.a64_amount k
  | .Oaddlimm n, [a1] => ii1 res a1 fun rd r1 => addimm64 rd r1 n k
  | .Onegl, [a1] => ii1 res a1 fun rd r1 => .Psub .X rd .XZR r1 .SOnone :: k
  | .Oneglshift s a, [a1] =>
      ii1 res a1 fun rd r1 => .Psub .X rd .XZR r1 (translShift s a.a64_amount) :: k
  | .Osubl, [a1, a2] => ii2 res a1 a2 fun rd r1 r2 => .Psub .X rd r1 r2 .SOnone :: k
  | .Osublshift s a, [a1, a2] =>
      ii2 res a1 a2 fun rd r1 r2 => .Psub .X rd r1 r2 (translShift s a.a64_amount) :: k
  | .Osublext x a, [a1, a2] =>
      ii2 res a1 a2 fun rd r1 r2 => arithExtended .Psubext (.Psub .X) rd r1 r2 x a.a64_amount k
  | .Omull, [a1, a2] => ii2 res a1 a2 fun rd r1 r2 => .Pmadd .X rd r1 r2 .XZR :: k
  | .Omulladd, [a1, a2, a3] =>
      ii3 res a1 a2 a3 fun rd r1 r2 r3 => .Pmadd .X rd r2 r3 r1 :: k
  | .Omullsub, [a1, a2, a3] =>
      ii3 res a1 a2 a3 fun rd r1 r2 r3 => .Pmsub .X rd r2 r3 r1 :: k
  | .Omullhs, [a1, a2] => ii2 res a1 a2 fun rd r1 r2 => .Psmulh rd r1 r2 :: k
  | .Omullhu, [a1, a2] => ii2 res a1 a2 fun rd r1 r2 => .Pumulh rd r1 r2 :: k
  | .Odivl, [a1, a2] => ii2 res a1 a2 fun rd r1 r2 => .Psdiv .X rd r1 r2 :: k
  | .Odivlu, [a1, a2] => ii2 res a1 a2 fun rd r1 r2 => .Pudiv .X rd r1 r2 :: k
  | .Oandl, [a1, a2] => ii2 res a1 a2 fun rd r1 r2 => .Pand .X rd r1 r2 .SOnone :: k
  | .Oandlshift s a, [a1, a2] =>
      ii2 res a1 a2 fun rd r1 r2 => .Pand .X rd r1 r2 (translShift s a.a64_amount) :: k
  | .Oandlimm n, [a1] =>
      ii1 res a1 fun rd r1 => logicalimm64 (.Pandimm .X) (.Pand .X) rd r1 n k
  | .Oorl, [a1, a2] => ii2 res a1 a2 fun rd r1 r2 => .Porr .X rd r1 r2 .SOnone :: k
  | .Oorlshift s a, [a1, a2] =>
      ii2 res a1 a2 fun rd r1 r2 => .Porr .X rd r1 r2 (translShift s a.a64_amount) :: k
  | .Oorlimm n, [a1] =>
      ii1 res a1 fun rd r1 => logicalimm64 (.Porrimm .X) (.Porr .X) rd r1 n k
  | .Oxorl, [a1, a2] => ii2 res a1 a2 fun rd r1 r2 => .Peor .X rd r1 r2 .SOnone :: k
  | .Oxorlshift s a, [a1, a2] =>
      ii2 res a1 a2 fun rd r1 r2 => .Peor .X rd r1 r2 (translShift s a.a64_amount) :: k
  | .Oxorlimm n, [a1] =>
      ii1 res a1 fun rd r1 => logicalimm64 (.Peorimm .X) (.Peor .X) rd r1 n k
  | .Onotl, [a1] => ii1 res a1 fun rd r1 => .Porn .X rd .XZR r1 .SOnone :: k
  | .Onotlshift s a, [a1] =>
      ii1 res a1 fun rd r1 => .Porn .X rd .XZR r1 (translShift s a.a64_amount) :: k
  | .Obicl, [a1, a2] => ii2 res a1 a2 fun rd r1 r2 => .Pbic .X rd r1 r2 .SOnone :: k
  | .Obiclshift s a, [a1, a2] =>
      ii2 res a1 a2 fun rd r1 r2 => .Pbic .X rd r1 r2 (translShift s a.a64_amount) :: k
  | .Oornl, [a1, a2] => ii2 res a1 a2 fun rd r1 r2 => .Porn .X rd r1 r2 .SOnone :: k
  | .Oornlshift s a, [a1, a2] =>
      ii2 res a1 a2 fun rd r1 r2 => .Porn .X rd r1 r2 (translShift s a.a64_amount) :: k
  | .Oeqvl, [a1, a2] => ii2 res a1 a2 fun rd r1 r2 => .Peon .X rd r1 r2 .SOnone :: k
  | .Oeqvlshift s a, [a1, a2] =>
      ii2 res a1 a2 fun rd r1 r2 => .Peon .X rd r1 r2 (translShift s a.a64_amount) :: k
  | .Oshll, [a1, a2] => ii2 res a1 a2 fun rd r1 r2 => .Plslv .X rd r1 r2 :: k
  | .Oshrl, [a1, a2] => ii2 res a1 a2 fun rd r1 r2 => .Pasrv .X rd r1 r2 :: k
  | .Oshrlu, [a1, a2] => ii2 res a1 a2 fun rd r1 r2 => .Plsrv .X rd r1 r2 :: k
  | .Oshrlximm n, [a1] => ii1 res a1 fun rd r1 => shrx64 rd r1 n k
  | .Ozextl s, [a1] => ii1 res a1 fun rd r1 => .Pubfiz .X rd r1 Integers.Int.zero s :: k
  | .Osextl s, [a1] => ii1 res a1 fun rd r1 => .Psbfiz .X rd r1 Integers.Int.zero s :: k
  | .Oshllzext s a, [a1] =>
      ii1 res a1 fun rd r1 => .Pubfiz .X rd r1 a.a64_amount
        (min s (Integers.Int64.zwordsize - Integers.Int.unsigned a.a64_amount)) :: k
  | .Oshllsext s a, [a1] =>
      ii1 res a1 fun rd r1 => .Psbfiz .X rd r1 a.a64_amount
        (min s (Integers.Int64.zwordsize - Integers.Int.unsigned a.a64_amount)) :: k
  | .Ozextshrl a s, [a1] =>
      ii1 res a1 fun rd r1 => .Pubfx .X rd r1 a.a64_amount
        (min s (Integers.Int64.zwordsize - Integers.Int.unsigned a.a64_amount)) :: k
  | .Osextshrl a s, [a1] =>
      ii1 res a1 fun rd r1 => .Psbfx .X rd r1 a.a64_amount
        (min s (Integers.Int64.zwordsize - Integers.Int.unsigned a.a64_amount)) :: k
  -- 64-bit floating-point arithmetic
  | .Onegf, [a1] => ff1 res a1 fun rd rs => .Pfneg .D rd rs :: k
  | .Oabsf, [a1] => ff1 res a1 fun rd rs => .Pfabs .D rd rs :: k
  | .Oaddf, [a1, a2] => ff2 res a1 a2 fun rd rs1 rs2 => .Pfadd .D rd rs1 rs2 :: k
  | .Osubf, [a1, a2] => ff2 res a1 a2 fun rd rs1 rs2 => .Pfsub .D rd rs1 rs2 :: k
  | .Omulf, [a1, a2] => ff2 res a1 a2 fun rd rs1 rs2 => .Pfmul .D rd rs1 rs2 :: k
  | .Odivf, [a1, a2] => ff2 res a1 a2 fun rd rs1 rs2 => .Pfdiv .D rd rs1 rs2 :: k
  -- 32-bit floating-point arithmetic
  | .Onegfs, [a1] => ff1 res a1 fun rd rs => .Pfneg .S rd rs :: k
  | .Oabsfs, [a1] => ff1 res a1 fun rd rs => .Pfabs .S rd rs :: k
  | .Oaddfs, [a1, a2] => ff2 res a1 a2 fun rd rs1 rs2 => .Pfadd .S rd rs1 rs2 :: k
  | .Osubfs, [a1, a2] => ff2 res a1 a2 fun rd rs1 rs2 => .Pfsub .S rd rs1 rs2 :: k
  | .Omulfs, [a1, a2] => ff2 res a1 a2 fun rd rs1 rs2 => .Pfmul .S rd rs1 rs2 :: k
  | .Odivfs, [a1, a2] => ff2 res a1 a2 fun rd rs1 rs2 => .Pfdiv .S rd rs1 rs2 :: k
  | .Osingleoffloat, [a1] => ff1 res a1 fun rd rs => .Pfcvtsd rd rs :: k
  | .Ofloatofsingle, [a1] => ff1 res a1 fun rd rs => .Pfcvtds rd rs :: k
  -- Conversions between int and float
  | .Ointoffloat, [a1] => if1 res a1 fun rd rs => .Pfcvtzs .W .D rd rs :: k
  | .Ointuoffloat, [a1] => if1 res a1 fun rd rs => .Pfcvtzu .W .D rd rs :: k
  | .Ofloatofint, [a1] => fi1 res a1 fun rd rs => .Pscvtf .D .W rd rs :: k
  | .Ofloatofintu, [a1] => fi1 res a1 fun rd rs => .Pucvtf .D .W rd rs :: k
  | .Ointofsingle, [a1] => if1 res a1 fun rd rs => .Pfcvtzs .W .S rd rs :: k
  | .Ointuofsingle, [a1] => if1 res a1 fun rd rs => .Pfcvtzu .W .S rd rs :: k
  | .Osingleofint, [a1] => fi1 res a1 fun rd rs => .Pscvtf .S .W rd rs :: k
  | .Osingleofintu, [a1] => fi1 res a1 fun rd rs => .Pucvtf .S .W rd rs :: k
  | .Olongoffloat, [a1] => if1 res a1 fun rd rs => .Pfcvtzs .X .D rd rs :: k
  | .Olonguoffloat, [a1] => if1 res a1 fun rd rs => .Pfcvtzu .X .D rd rs :: k
  | .Ofloatoflong, [a1] => fi1 res a1 fun rd rs => .Pscvtf .D .X rd rs :: k
  | .Ofloatoflongu, [a1] => fi1 res a1 fun rd rs => .Pucvtf .D .X rd rs :: k
  | .Olongofsingle, [a1] => if1 res a1 fun rd rs => .Pfcvtzs .X .S rd rs :: k
  | .Olonguofsingle, [a1] => if1 res a1 fun rd rs => .Pfcvtzu .X .S rd rs :: k
  | .Osingleoflong, [a1] => fi1 res a1 fun rd rs => .Pscvtf .S .X rd rs :: k
  | .Osingleoflongu, [a1] => fi1 res a1 fun rd rs => .Pucvtf .S .X rd rs :: k
  -- Boolean tests
  | .Ocmp c, _ => do
      let rd ← iregOf res
      translCond c args (.Pcset rd (condForCond c) :: k)
  -- Conditional move
  | .Osel cmp _, a1 :: a2 :: args =>
      match pregOf res with
      | .IR r => do
          let r1 ← iregOf a1; let r2 ← iregOf a2
          if r1 = r2 then pure (.Pmov r r1 :: k)
          else translCond cmp args (.Pcsel r r1 r2 (condForCond cmp) :: k)
      | .FR r => do
          let r1 ← fregOf a1; let r2 ← fregOf a2
          if r1 = r2 then pure (.Pfmov r r1 :: k)
          else translCond cmp args (.Pfsel r r1 r2 (condForCond cmp) :: k)
      | _ => .Error "Asmgen.Osel"
  | _, _ => .Error "Asmgen.transl_op"

/-! ## Addressing modes, loads and stores -/

/-- `Asmgen.offset_representable` -/
def offsetRepresentable (sz : Z) (ofs : Integers.Int64) : Bool :=
  let isz := Integers.Int64.repr sz
  -- either unscaled 9-bit signed
  Integers.Int64.eq ofs (Integers.Int64.sign_ext 9 ofs) ||
  -- or scaled 12-bit unsigned
  (Integers.Int64.eq (Integers.Int64.modu ofs isz) Integers.Int64.zero &&
    Integers.Int64.ltu ofs (Integers.Int64.shl isz (Integers.Int64.repr 12)))

/-- `Asmgen.transl_addressing` -/
def translAddressing (o : Options) (sz : Z) (addr : Op.Addressing) (args : List Mreg)
    (insn : Asm.Addressing → Instruction) (k : Code) : Res Code :=
  match addr, args with
  | .Aindexed ofs, [a1] => do
      let r1 ← iregOf a1
      if offsetRepresentable sz ofs then pure (insn (.ADimm r1 ofs) :: k)
      else pure (loadimm64 .X16 ofs (insn (.ADreg r1 .X16) :: k))
  | .Aindexed2, [a1, a2] => do
      let r1 ← iregOf a1; let r2 ← iregOf a2
      pure (insn (.ADreg r1 r2) :: k)
  | .Aindexed2shift a, [a1, a2] => do
      let r1 ← iregOf a1; let r2 ← iregOf a2
      let a := a.a64_amount
      if Integers.Int.eq a Integers.Int.zero then pure (insn (.ADreg r1 r2) :: k)
      else if Integers.Int.eq (Integers.Int.shl Integers.Int.one a) (Integers.Int.repr sz) then
        pure (insn (.ADlsl r1 r2 a) :: k)
      else pure (.Padd .X .X16 r1 r2 (.SOlsl a) :: insn (.ADimm (.RR1 .X16) Integers.Int64.zero) :: k)
  | .Aindexed2ext x a, [a1, a2] => do
      let r1 ← iregOf a1; let r2 ← iregOf a2
      let a := a.a64_amount
      if Integers.Int.eq a Integers.Int.zero ||
          Integers.Int.eq (Integers.Int.shl Integers.Int.one a) (Integers.Int.repr sz) then
        pure (insn (match x with
          | .Xsgn32 => .ADsxt r1 r2 a
          | .Xuns32 => .ADuxt r1 r2 a) :: k)
      else
        pure (arithExtended .Paddext (.Padd .X) .X16 r1 r2 x a
          (insn (.ADimm (.RR1 .X16) Integers.Int64.zero) :: k))
  | .Aglobal id ofs, [] =>
      if !(o.symbolIsRelocatable id) then
        if Integers.Ptrofs.eq (Integers.Ptrofs.modu ofs (Integers.Ptrofs.repr sz))
            Integers.Ptrofs.zero && o.symbolIsAligned id sz then
          .OK (.Padrp .X16 id ofs :: insn (.ADadr (.RR1 .X16) id ofs) :: k)
        else .OK (loadsymbol o .X16 id ofs (insn (.ADimm (.RR1 .X16) Integers.Int64.zero) :: k))
      else .Error "Assertion failed"
  | .Ainstack ofs, [] =>
      let ofs := Integers.Ptrofs.to_int64 ofs
      if offsetRepresentable sz ofs then .OK (insn (.ADimm .XSP ofs) :: k)
      else .OK (loadimm64 .X16 ofs (insn (.ADreg .XSP .X16) :: k))
  | _, _ => .Error "Asmgen.transl_addressing"

/-- `Asmgen.transl_load` -/
def translLoad (o : Options) (chunk : Chunk) (addr : Op.Addressing) (args : List Mreg)
    (dst : Mreg) (k : Code) : Res Code :=
  match chunk with
  | .Mint8unsigned => do let rd ← iregOf dst; translAddressing o 1 addr args (.Pldrb .W rd) k
  | .Mint8signed => do let rd ← iregOf dst; translAddressing o 1 addr args (.Pldrsb .W rd) k
  | .Mint16unsigned => do let rd ← iregOf dst; translAddressing o 2 addr args (.Pldrh .W rd) k
  | .Mint16signed => do let rd ← iregOf dst; translAddressing o 2 addr args (.Pldrsh .W rd) k
  | .Mint32 => do let rd ← iregOf dst; translAddressing o 4 addr args (.Pldrw rd) k
  | .Mint64 => do let rd ← iregOf dst; translAddressing o 8 addr args (.Pldrx rd) k
  | .Mfloat32 => do let rd ← fregOf dst; translAddressing o 4 addr args (.Pldrs rd) k
  | .Mfloat64 => do let rd ← fregOf dst; translAddressing o 8 addr args (.Pldrd rd) k
  | .Many32 => do let rd ← iregOf dst; translAddressing o 4 addr args (.Pldrw_a rd) k
  | .Many64 => do let rd ← iregOf dst; translAddressing o 8 addr args (.Pldrx_a rd) k
  | _ => .Error "Asmgen.transl_load"

/-- `Asmgen.transl_store` -/
def translStore (o : Options) (chunk : Chunk) (addr : Op.Addressing) (args : List Mreg)
    (src : Mreg) (k : Code) : Res Code :=
  match chunk with
  | .Mint8unsigned => do let r1 ← iregOf src; translAddressing o 1 addr args (.Pstrb r1) k
  | .Mint16unsigned => do let r1 ← iregOf src; translAddressing o 2 addr args (.Pstrh r1) k
  | .Mint32 => do let r1 ← iregOf src; translAddressing o 4 addr args (.Pstrw r1) k
  | .Mint64 => do let r1 ← iregOf src; translAddressing o 8 addr args (.Pstrx r1) k
  | .Mfloat32 => do let r1 ← fregOf src; translAddressing o 4 addr args (.Pstrs r1) k
  | .Mfloat64 => do let r1 ← fregOf src; translAddressing o 8 addr args (.Pstrd r1) k
  | .Many32 => do let r1 ← iregOf src; translAddressing o 4 addr args (.Pstrw_a r1) k
  | .Many64 => do let r1 ← iregOf src; translAddressing o 8 addr args (.Pstrx_a r1) k
  | _ => .Error "Asmgen.transl_store"

/-- `Asmgen.indexed_memory_access` -/
def indexedMemoryAccess (insn : Asm.Addressing → Instruction) (sz : Z) (base : Iregsp)
    (ofs : Integers.Ptrofs) (k : Code) : Code :=
  let ofs := Integers.Ptrofs.to_int64 ofs
  if offsetRepresentable sz ofs then insn (.ADimm base ofs) :: k
  else loadimm64 .X16 ofs (insn (.ADreg base .X16) :: k)

/-- `Asmgen.loadind` -/
def loadind (base : Iregsp) (ofs : Integers.Ptrofs) (ty : ATyp) (dst : Mreg) (k : Code) :
    Res Code :=
  match ty, pregOf dst with
  | .Tint, .IR rd => .OK (indexedMemoryAccess (.Pldrw rd) 4 base ofs k)
  | .Tlong, .IR rd => .OK (indexedMemoryAccess (.Pldrx rd) 8 base ofs k)
  | .Tsingle, .FR rd => .OK (indexedMemoryAccess (.Pldrs rd) 4 base ofs k)
  | .Tfloat, .FR rd => .OK (indexedMemoryAccess (.Pldrd rd) 8 base ofs k)
  | .Tany32, .IR rd => .OK (indexedMemoryAccess (.Pldrw_a rd) 4 base ofs k)
  | .Tany64, .IR rd => .OK (indexedMemoryAccess (.Pldrx_a rd) 8 base ofs k)
  | .Tany64, .FR rd => .OK (indexedMemoryAccess (.Pldrd_a rd) 8 base ofs k)
  | _, _ => .Error "Asmgen.loadind"

/-- `Asmgen.storeind` -/
def storeind (src : Mreg) (base : Iregsp) (ofs : Integers.Ptrofs) (ty : ATyp) (k : Code) :
    Res Code :=
  match ty, pregOf src with
  | .Tint, .IR rd => .OK (indexedMemoryAccess (.Pstrw rd) 4 base ofs k)
  | .Tlong, .IR rd => .OK (indexedMemoryAccess (.Pstrx rd) 8 base ofs k)
  | .Tsingle, .FR rd => .OK (indexedMemoryAccess (.Pstrs rd) 4 base ofs k)
  | .Tfloat, .FR rd => .OK (indexedMemoryAccess (.Pstrd rd) 8 base ofs k)
  | .Tany32, .IR rd => .OK (indexedMemoryAccess (.Pstrw_a rd) 4 base ofs k)
  | .Tany64, .IR rd => .OK (indexedMemoryAccess (.Pstrx_a rd) 8 base ofs k)
  | .Tany64, .FR rd => .OK (indexedMemoryAccess (.Pstrd_a rd) 8 base ofs k)
  | _, _ => .Error "Asmgen.storeind"

/-- `Asmgen.loadptr` -/
def loadptr (base : Iregsp) (ofs : Integers.Ptrofs) (dst : Ireg) (k : Code) : Code :=
  indexedMemoryAccess (.Pldrx dst) 8 base ofs k

/-- `Asmgen.storeptr` -/
def storeptr (src : Ireg) (base : Iregsp) (ofs : Integers.Ptrofs) (k : Code) : Code :=
  indexedMemoryAccess (.Pstrx src) 8 base ofs k

/-! ## Function epilogue and instructions -/

/-- `Asmgen.make_epilogue` -/
def makeEpilogue (f : Mach.Function) (k : Code) : Code :=
  loadptr .XSP f.fn_retaddr_ofs RA (.Pfreeframe f.fn_stacksize f.fn_link_ofs :: k)

/-- `Asmgen.transl_instr` -/
def translInstr (o : Options) (f : Mach.Function) (i : Mach.Instruction) (r15IsParent : Bool)
    (k : Code) : Res Code :=
  match i with
  | .Mgetstack ofs ty dst => loadind .XSP ofs ty dst k
  | .Msetstack src ofs ty => storeind src .XSP ofs ty k
  | .Mgetparam ofs ty dst => do
      -- load via the frame pointer if it is valid
      let c ← loadind (.RR1 .X15) ofs ty dst k
      pure (if r15IsParent then c else loadptr .XSP f.fn_link_ofs .X15 c)
  | .Mop op args res => translOp o op args res k
  | .Mload chunk addr args dst => translLoad o chunk addr args dst k
  | .Mstore chunk addr args src => translStore o chunk addr args src k
  | .Mcall sig (.inl r) => do let r1 ← iregOf r; pure (.Pblr r1 sig :: k)
  | .Mcall sig (.inr symb) => .OK (.Pbl symb sig :: k)
  | .Mtailcall sig (.inl r) => do
      let r1 ← iregOf r; pure (makeEpilogue f (.Pbr r1 sig :: k))
  | .Mtailcall sig (.inr symb) => .OK (makeEpilogue f (.Pbs symb sig :: k))
  | .Mbuiltin ef args res =>
      .OK (.Pbuiltin ef (args.map (BuiltinArg.map pregOf)) (BuiltinRes.map pregOf res) :: k)
  | .Mlabel lbl => .OK (.Plabel lbl :: k)
  | .Mgoto lbl => .OK (.Pb lbl :: k)
  | .Mcond cond args lbl => translCondBranch cond args lbl k
  | .Mjumptable arg tbl => do let r ← iregOf arg; pure (.Pbtbl r tbl :: k)
  | .Mreturn => .OK (makeEpilogue f (.Pret RA :: k))

/-- `Asmgen.it1_is_parent`: does `X15` still hold the parent's stack
    pointer after instruction `i`? -/
def it1IsParent (before : Bool) (i : Mach.Instruction) : Bool :=
  match i with
  | .Msetstack .. => before
  | .Mgetparam _ _ dst => !(decide (dst = .R15))
  | .Mop _ _ res => before && !(decide (res = .R15))
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
         fn_code := .Pallocframe f.fn_stacksize f.fn_link_ofs f.fn_retaddr_ofs ::
           .Pcfi_rel_offset (Integers.Ptrofs.to_int f.fn_retaddr_ofs) :: c }

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
theorem transl_code'_transl_code (o : Options) (f : Mach.Function)
    (il : List Mach.Instruction) (it1p : Bool) :
    translCode' o f il it1p = translCode o f il it1p := by
  rw [translCode', translCodeRec_spec]
  cases translCode o f il it1p <;> rfl

end Asmgen
end CC
