/-
  [x86-64 instance of `CCLib/backend/CSE.lean`: the same development, in
  namespace `CC.X86`, over the x86-64 operators, registers and conventions.]

  Common subexpression elimination over RTL, by value numbering over
  extended basic blocks — port of `backend/CSE.v` (definitions).

  Ported: `valnum_reg`, `valnum_regs`, `valnum_builtin_arg`,
  `valnum_builtin_args`, `find_valnum_rhs`, `find_valnum_rhs'`,
  `find_valnum_num`, `reg_valnum`, `regs_valnums`, `find_rhs`,
  `forget_reg`, `update_reg`, `add_rhs`, `add_op`, `add_load`,
  `add_builtin`, `set_unknown`, `set_res_unknown`, `kill_eqs`,
  `kill_equations`, `filter_loads`, `kill_all_loads`,
  `filter_after_store`, `kill_loads_after_store`, `filter_cheap`,
  `kill_cheap_computations`, `store_normalized_range`,
  `add_store_result`, `kill_loads_after_storebytes`, `shift_memcpy_eq`,
  `add_memcpy_eqs`, `add_memcpy`, `reduce_rec`, `reduce`,
  `Numbering.top`, `transfer`, `analyze` (with the extended-basic-block
  solver of `KildallBBlock.lean`), `transf_instr`, `transf_code`,
  `vanalyze`, `transf_function`, `transf_fundef`, `transf_program`.
  Not ported: the order `Numbering.ge` (stated with `numbering_holds`) and
  `CSEproof.v`.

  Differences from Rocq: the OCaml parameters of the value analysis are
  given by `ValueAOp.Options`, and `Archi.abi` by `abi`.
-/
import CCLib.x86.CombineOp
import CCLib.x86.CSEdomain
import CCLib.backend.KildallBBlock
import CCLib.x86.ValueAnalysis
import CCLib.common.EventsBuiltinArgs
import CCLib.x86.Tailcall

namespace CC
namespace X86


namespace CSE

open ValueDomain ValueAnalysis RTL CSEdomain CombineOp Op

/-! ## Operations on value numberings -/

/-- `CSE.valnum_reg` -/
def valnumReg (n : Numbering) (r : Reg) : Numbering × Valnum :=
  match n.num_reg.get r with
  | some v => (n, v)
  | none =>
      let v := n.num_next
      ({ num_next := v.succ, num_eqs := n.num_eqs, num_reg := n.num_reg.set r v,
         num_val := n.num_val.set v [r] }, v)

/-- `CSE.valnum_regs` -/
def valnumRegs (n : Numbering) : List Reg → Numbering × List Valnum
  | [] => (n, [])
  | r1 :: rs =>
      let (n1, v1) := valnumReg n r1
      let (ns, vs) := valnumRegs n1 rs
      (ns, v1 :: vs)

/-- `CSE.valnum_builtin_arg` -/
def valnumBuiltinArg (n : Numbering) : BuiltinArg Reg → Numbering × BuiltinArg Valnum
  | .BA r => let (n, v) := valnumReg n r; (n, .BA v)
  | .BA_int i => (n, .BA_int i)
  | .BA_long i => (n, .BA_long i)
  | .BA_float f => (n, .BA_float f)
  | .BA_single f => (n, .BA_single f)
  | .BA_loadstack chunk ofs => (n, .BA_loadstack chunk ofs)
  | .BA_addrstack ofs => (n, .BA_addrstack ofs)
  | .BA_loadglobal chunk id ofs => (n, .BA_loadglobal chunk id ofs)
  | .BA_addrglobal id ofs => (n, .BA_addrglobal id ofs)
  | .BA_splitlong a1 a2 =>
      let (n, v1) := valnumBuiltinArg n a1
      let (n, v2) := valnumBuiltinArg n a2
      (n, .BA_splitlong v1 v2)
  | .BA_addptr a1 a2 =>
      let (n, v1) := valnumBuiltinArg n a1
      let (n, v2) := valnumBuiltinArg n a2
      (n, .BA_addptr v1 v2)

/-- `CSE.valnum_builtin_args` -/
def valnumBuiltinArgs (n : Numbering) : List (BuiltinArg Reg) → Numbering × List (BuiltinArg Valnum)
  | [] => (n, [])
  | arg1 :: args =>
      let (n1, v1) := valnumBuiltinArg n arg1
      let (ns, vs) := valnumBuiltinArgs n1 args
      (ns, v1 :: vs)

/-- `CSE.find_valnum_rhs` -/
def findValnumRhs (r : Rhs) : List Equation → Option Valnum
  | [] => none
  | .Eq v str r' :: eqs1 => if str && compatRhs r r' then some v else findValnumRhs r eqs1

/-- `CSE.find_valnum_rhs'` -/
def findValnumRhs' (r : Rhs) : List Equation → Option Valnum
  | [] => none
  | .Eq v _ r' :: eqs1 => if compatRhs r r' then some v else findValnumRhs' r eqs1

/-- `CSE.find_valnum_num` -/
def findValnumNum (v : Valnum) : List Equation → Option Rhs
  | [] => none
  | .Eq v' str r' :: eqs1 => if str && decide (v = v') then some r' else findValnumNum v eqs1

/-- `CSE.reg_valnum` -/
def regValnum (n : Numbering) (vn : Valnum) : Option Reg :=
  match n.num_val.get vn with
  | [] => none
  | r :: _ => some r

/-- `CSE.regs_valnums` -/
def regsValnums (n : Numbering) : List Valnum → Option (List Reg)
  | [] => some []
  | v1 :: vs =>
      match regValnum n v1, regsValnums n vs with
      | some r1, some rs => some (r1 :: rs)
      | _, _ => none

/-- `CSE.find_rhs` -/
def findRhs (n : Numbering) (rh : Rhs) : Option Reg :=
  match findValnumRhs' rh n.num_eqs with
  | none => none
  | some vres => regValnum n vres

/-- `CSE.forget_reg` -/
def forgetReg (n : Numbering) (rd : Reg) : PMap (List Reg) :=
  match n.num_reg.get rd with
  | none => n.num_val
  | some v => n.num_val.set v ((n.num_val.get v).filter (fun r => r != rd))

/-- `CSE.update_reg` -/
def updateReg (n : Numbering) (rd : Reg) (vn : Valnum) : PMap (List Reg) :=
  let nv := forgetReg n rd
  nv.set vn (rd :: nv.get vn)

/-- `CSE.add_rhs` -/
def addRhs (n : Numbering) (rd : Reg) (rh : Rhs) : Numbering :=
  match findValnumRhs rh n.num_eqs with
  | some vres =>
      { num_next := n.num_next, num_eqs := n.num_eqs, num_reg := n.num_reg.set rd vres,
        num_val := updateReg n rd vres }
  | none =>
      { num_next := n.num_next.succ, num_eqs := .Eq n.num_next true rh :: n.num_eqs,
        num_reg := n.num_reg.set rd n.num_next, num_val := updateReg n rd n.num_next }

/-- `CSE.add_op` -/
def addOp (n : Numbering) (rd : Reg) (op : Operation) (rs : List Reg) : Numbering :=
  match isMoveOperation op rs with
  | some r =>
      let (n1, v) := valnumReg n r
      { num_next := n1.num_next, num_eqs := n1.num_eqs, num_reg := n1.num_reg.set rd v,
        num_val := updateReg n1 rd v }
  | none =>
      let (n1, vs) := valnumRegs n rs
      addRhs n1 rd (.Op op vs)

/-- `CSE.add_load` -/
def addLoad (n : Numbering) (rd : Reg) (chunk : Chunk) (addr : Addressing) (rs : List Reg)
    (p : Aptr) : Numbering :=
  let (n1, vs) := valnumRegs n rs
  addRhs n1 rd (.Load chunk addr vs p)

/-- `CSE.add_builtin` -/
def addBuiltin (n : Numbering) (dst : BuiltinRes Reg) (bf : Builtins.BuiltinFunction)
    (args : List (BuiltinArg Reg)) : Numbering :=
  match dst with
  | .BR rd =>
      let (n1, args1) := valnumBuiltinArgs n args
      addRhs n1 rd (.Builtin bf args1)
  | _ => n

/-- `CSE.set_unknown` -/
def setUnknown (n : Numbering) (rd : Reg) : Numbering :=
  { num_next := n.num_next, num_eqs := n.num_eqs, num_reg := n.num_reg.remove rd,
    num_val := forgetReg n rd }

/-- `CSE.set_res_unknown` -/
def setResUnknown (n : Numbering) (res : BuiltinRes Reg) : Numbering :=
  match res with
  | .BR r => setUnknown n r
  | _ => n

/-- `CSE.kill_eqs` -/
def killEqs (pred : Rhs → Bool) : List Equation → List Equation
  | [] => []
  | (.Eq l strict r) :: rem =>
      if pred r then killEqs pred rem else .Eq l strict r :: killEqs pred rem

/-- `CSE.kill_equations` -/
def killEquations (pred : Rhs → Bool) (n : Numbering) : Numbering :=
  { n with num_eqs := killEqs pred n.num_eqs }

/-- `CSE.filter_loads` -/
def filterLoads (r : Rhs) : Bool :=
  match r with
  | .Op op _ => opDependsOnMemory op
  | .Load _ _ _ _ => true
  | .Builtin _ args => args.any builtinArgDependsOnMemory

/-- `CSE.kill_all_loads` -/
def killAllLoads (n : Numbering) : Numbering := killEquations filterLoads n

/-- `CSE.filter_after_store` -/
def filterAfterStore (_n : Numbering) (p : Aptr) (sz : Z) (r : Rhs) : Bool :=
  match r with
  | .Op op _ => opDependsOnMemory op
  | .Load chunk _ _ q => !(pdisjoint q (sizeChunk chunk) p sz)
  | .Builtin _ args => args.any builtinArgDependsOnMemory

section
variable (o : ValueAOp.Options)

/-- `CSE.kill_loads_after_store` -/
def killLoadsAfterStore (app : VAState) (n : Numbering) (chunk : Chunk) (addr : Addressing)
    (args : List Reg) : Numbering :=
  let p := aaddressing o app addr args
  killEquations (filterAfterStore n p (sizeChunk chunk)) n

end

/-- `CSE.filter_cheap`: `Op` and `Load` are cheap, `Builtin` is not. -/
def filterCheap (r : Rhs) : Bool :=
  match r with
  | .Op _ _ => true
  | .Load _ _ _ _ => true
  | .Builtin _ _ => false

/-- `CSE.kill_cheap_computations` -/
def killCheapComputations (n : Numbering) : Numbering := killEquations filterCheap n

/-- `CSE.store_normalized_range` -/
def storeNormalizedRange (chunk : Chunk) : Aval :=
  match chunk with
  | .Mbool => .Uns .Ptop 1
  | .Mint8signed => .Sgn .Ptop 8
  | .Mint8unsigned => .Uns .Ptop 8
  | .Mint16signed => .Sgn .Ptop 16
  | .Mint16unsigned => .Uns .Ptop 16
  | _ => Vtop

section
variable (o : ValueAOp.Options)

/-- `CSE.add_store_result` -/
def addStoreResult (app : VAState) (n : Numbering) (chunk : Chunk) (addr : Addressing)
    (rargs : List Reg) (rsrc : Reg) : Numbering :=
  if vincl (avalue app rsrc) (storeNormalizedRange chunk) then
    let (n1, vsrc) := valnumReg n rsrc
    let (n2, vargs) := valnumRegs n1 rargs
    { num_next := n2.num_next,
      num_eqs := .Eq vsrc false (.Load chunk addr vargs (aaddressing o app addr rargs)) :: n2.num_eqs,
      num_reg := n2.num_reg, num_val := n2.num_val }
  else n

end

/-- `CSE.kill_loads_after_storebytes` -/
def killLoadsAfterStorebytes (n : Numbering) (dst : Aptr) (sz : Z) : Numbering :=
  killEquations (filterAfterStore n dst sz) n

/-- `CSE.shift_memcpy_eq` -/
def shiftMemcpyEq (src sz delta : Z) (e : Equation) : Option Equation :=
  match e with
  | .Eq l strict (.Load chunk (.Ainstack i) _ _) =>
      let i := Integers.Ptrofs.unsigned i
      let j := i + delta
      if decide (src ≤ i) && decide (i + sizeChunk chunk ≤ src + sz) &&
          decide (Int.emod delta (alignChunk chunk) = 0) && decide (0 ≤ j) &&
          decide (j + sizeChunk chunk ≤ Integers.Ptrofs.modulus)
      then some (.Eq l strict (.Load chunk (.Ainstack (Integers.Ptrofs.repr j)) []
        (.Stk (Integers.Ptrofs.repr j))))
      else none
  | _ => none

/-- `CSE.add_memcpy_eqs` -/
def addMemcpyEqs (src sz delta : Z) : List Equation → List Equation → List Equation
  | [], eqs2 => eqs2
  | e :: eqs, eqs2 =>
      match shiftMemcpyEq src sz delta e with
      | none => addMemcpyEqs src sz delta eqs eqs2
      | some e' => e' :: addMemcpyEqs src sz delta eqs eqs2

/-- `CSE.add_memcpy`: only copies between stack locations are tracked. -/
def addMemcpy (n1 n2 : Numbering) (asrc adst : Aptr) (sz : Z) : Numbering :=
  match asrc, adst with
  | .Stk src, .Stk dst =>
      let eqs := addMemcpyEqs (Integers.Ptrofs.unsigned src) sz
        (Integers.Ptrofs.unsigned dst - Integers.Ptrofs.unsigned src) n1.num_eqs n2.num_eqs
      { n2 with num_eqs := eqs }
  | _, _ => n2

/-! ## Reduction of operations, addressing modes and conditions -/

section REDUCE
variable {A : Type} (f : (Valnum → Option Rhs) → A → List Valnum → Option (A × List Valnum))
  (n : Numbering)

/-- `CSE.reduce_rec` -/
def reduceRec : Nat → A → List Valnum → Option (A × List Reg)
  | 0, _, _ => none
  | niter' + 1, op, args =>
      match f (fun v => findValnumNum v n.num_eqs) op args with
      | none => none
      | some (op', args') =>
          match reduceRec niter' op' args' with
          | none =>
              match regsValnums n args' with
              | some rl => some (op', rl)
              | none => none
          | some res => some res

/-- `CSE.reduce` -/
def reduce (op : A) (rl : List Reg) (vl : List Valnum) : A × List Reg :=
  match reduceRec f n 4 op vl with
  | none => (op, rl)
  | some res => res

end REDUCE

/-- `CSE.Numbering.top` -/
def numberingTop : Numbering := emptyNumbering

/-! ## The static analysis -/

section
variable (o : ValueAOp.Options)

/-- `CSE.transfer`: the numbering after the instruction at `pc`. -/
def transfer (f : RTL.Function) (dm : Defmap) (approx : PMap VAState) (pc : Node)
    (before : Numbering) : Numbering :=
  match f.fn_code.get pc with
  | none => before
  | some i =>
      match i with
      | .Inop _ => before
      | .Iop op args res _ => addOp before res op args
      | .Iload chunk addr args dst _ =>
          addLoad before dst chunk addr args (aaddressing o (approx.get pc) addr args)
      | .Istore chunk addr args src _ =>
          let app := approx.get pc
          let n := killLoadsAfterStore o app before chunk addr args
          addStoreResult o app n chunk addr args src
      | .Icall _ ros args res _ =>
          match isKnownRuntimeFunction dm ros with
          | none => emptyNumbering
          | some bf =>
              let n := killCheapComputations before
              addBuiltin n (.BR res) bf (args.map .BA)
      | .Itailcall _ _ _ => emptyNumbering
      | .Ibuiltin ef args res _ =>
          match ef with
          | .EF_external _ _ | .EF_runtime _ _ | .EF_malloc | .EF_free | .EF_inline_asm _ _ _ =>
              emptyNumbering
          | .EF_vstore _ => setResUnknown (killAllLoads before) res
          | .EF_builtin name sg =>
              match Builtins.lookupBuiltinFunction name sg with
              | some bf => addBuiltin before res bf args
              | none => setResUnknown (killAllLoads before) res
          | .EF_memcpy sz _ =>
              match args with
              | [dst, src] =>
                  let app := approx.get pc
                  let adst := aaddrArg o app dst
                  let asrc := aaddrArg o app src
                  let n := killLoadsAfterStorebytes before adst sz
                  setResUnknown (addMemcpy before n asrc adst sz) res
              | _ => emptyNumbering
          | .EF_vload _ | .EF_annot _ _ _ | .EF_annot_val _ _ _ | .EF_debug _ _ _ =>
              setResUnknown before res
      | .Icond _ _ _ _ => before
      | .Ijumptable _ _ => before
      | .Ireturn _ => before

/-- `CSE.analyze`: extended-basic-block propagation of numberings. -/
def analyze (f : RTL.Function) (dm : Defmap) (approx : PMap VAState) :
    Option (PMap Numbering) :=
  Kildall.BBlock.fixpoint numberingTop f.fn_code successorsInstr (transfer o f dm approx)
    f.fn_entrypoint

end

/-! ## Code transformation -/

/-- `CSE.transf_instr` -/
def transfInstr (dm : Defmap) (n : Numbering) (instr : Instruction) : Instruction :=
  match instr with
  | .Iop op args res s =>
      if isTrivialOp op then instr
      else
        let (n1, vl) := valnumRegs n args
        match findRhs n1 (.Op op vl) with
        | some r => .Iop .Omove [r] res s
        | none =>
            let (op', args') := reduce combineOp n1 op args vl
            .Iop op' args' res s
  | .Iload chunk addr args dst s =>
      let (n1, vl) := valnumRegs n args
      match findRhs n1 (.Load chunk addr vl .Ptop) with
      | some r => .Iop .Omove [r] dst s
      | none =>
          let (addr', args') := reduce combineAddr n1 addr args vl
          .Iload chunk addr' args' dst s
  | .Istore chunk addr args src s =>
      let (n1, vl) := valnumRegs n args
      let (addr', args') := reduce combineAddr n1 addr args vl
      .Istore chunk addr' args' src s
  | .Icall _ ros args res s =>
      match isKnownRuntimeFunction dm ros with
      | none => instr
      | some bf =>
          let (n1, args') := valnumBuiltinArgs n (args.map .BA)
          match findRhs n1 (.Builtin bf args') with
          | some r => .Iop .Omove [r] res s
          | none => instr
  | .Ibuiltin (.EF_builtin name sg) args (.BR res) s =>
      match Builtins.lookupBuiltinFunction name sg with
      | some bf =>
          let (n1, args') := valnumBuiltinArgs n args
          match findRhs n1 (.Builtin bf args') with
          | some r => .Iop .Omove [r] res s
          | none => instr
      | none => instr
  | .Icond cond args s1 s2 =>
      let (n1, vl) := valnumRegs n args
      match combineCond' cond vl with
      | some b => .Inop (if b then s1 else s2)
      | none =>
          let (cond', args') := reduce combineCond n1 cond args vl
          .Icond cond' args' s1 s2
  | _ => instr

/-- `CSE.transf_code` -/
def transfCode (dm : Defmap) (approxs : PMap Numbering) (instrs : Code) : Code :=
  PTree.map (fun pc instr => transfInstr dm (approxs.get pc) instr) instrs

section
variable (o : ValueAOp.Options)

/-- `CSE.vanalyze` -/
def vanalyze (rm : Romem) (f : RTL.Function) : PMap VAState := ValueAnalysis.analyze o  rm f

/-- `CSE.transf_function` -/
def transfFunction (dm : Defmap) (rm : Romem) (f : RTL.Function) : Res RTL.Function :=
  let approx := vanalyze o  rm f
  match analyze o f dm approx with
  | none => .Error "CSE failure"
  | some approxs =>
      .OK { fn_sig := f.fn_sig, fn_params := f.fn_params, fn_stacksize := f.fn_stacksize,
            fn_code := transfCode dm approxs f.fn_code, fn_entrypoint := f.fn_entrypoint }

/-- `CSE.transf_fundef` -/
def transfFundef (dm : Defmap) (rm : Romem) (f : RTL.Fundef) : Res RTL.Fundef :=
  ASTFundef.transfPartial (transfFunction o  dm rm) f

/-- `CSE.transf_program` -/
def transfProgram (p : RTL.Program) : Res RTL.Program :=
  transformPartialProgram (transfFundef o  p.defmap (romemFor o p)) p

end

end CSE
end X86
end CC
