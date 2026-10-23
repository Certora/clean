/-
  Checks for the RTL optimisations (`Constprop`, `CSE`, `Deadcode`) and
  for the pipeline glue of `Compiler.lean`.  The `#guard`s are evaluated
  when this file is built.
-/
import CCLib.driver.Compiler

namespace OptimCheck
open CC RTL

def P (n : Nat) : Positive := Positive.ofNat n

def sig2 : Signature := { sig_args := [.Xint, .Xint], sig_res := .Xint, sig_cc := default }

def mkFun (code : RTL.Code) (entry : Nat) : RTL.Function :=
  { fn_sig := sig2, fn_params := [P 1, P 2], fn_stacksize := 0, fn_code := code,
    fn_entrypoint := P entry }

def describe (i : Option Instruction) : String :=
  match i with
  | some (.Inop _) => "nop"
  | some (.Iop .Omove [r] _ _) => s!"move {r.toNat}"
  | some (.Iop (.Ointconst n) [] _ _) => s!"const {Integers.Int.unsigned n}"
  | some (.Iop _ _ _ _) => "op"
  | some (.Ireturn _) => "return"
  | _ => "other"

/-! Constant propagation: `r3 := 2; r4 := r3 + 3; return r4` turns the
    addition into the constant `5`. -/

def cpCode : RTL.Code :=
  ((PTree.empty.set (P 3) (.Iop (.Ointconst (Integers.Int.repr 2)) [] (P 3) (P 2))).set
    (P 2) (.Iop (.Oaddimm (Integers.Int.repr 3)) [P 3] (P 4) (P 1))).set
    (P 1) (.Ireturn (some (P 4)))

#guard (match Constprop.transfFunction {} .AAPCS64 PTree.empty (mkFun cpCode 3) with
  | f => describe (f.fn_code.get (P 2))) == "const 5"

/-! CSE: the second `r1 + r2` becomes a move from `r3`. -/

def cseCode : RTL.Code :=
  (((PTree.empty.set (P 4) (.Iop .Oadd [P 1, P 2] (P 3) (P 3))).set
    (P 3) (.Iop .Oadd [P 1, P 2] (P 4) (P 2))).set
    (P 2) (.Iop .Osub [P 3, P 4] (P 5) (P 1))).set
    (P 1) (.Ireturn (some (P 5)))

#guard (match CSE.transfFunction {} .AAPCS64 PTree.empty PTree.empty (mkFun cseCode 4) with
  | .OK f => describe (f.fn_code.get (P 3))
  | .Error e => e) == "move 3"

/-! Dead code elimination: the unused subtraction becomes a `nop`. -/

def dcCode : RTL.Code :=
  ((PTree.empty.set (P 4) (.Iop .Oadd [P 1, P 2] (P 3) (P 3))).set
    (P 3) (.Iop .Osub [P 1, P 2] (P 6) (P 2))).set
    (P 2) (.Ireturn (some (P 3)))

#guard (match Deadcode.transfFunction {} .AAPCS64 PTree.empty PTree.empty (mkFun dcCode 4) with
  | .OK f => (describe (f.fn_code.get (P 4)), describe (f.fn_code.get (P 3)))
  | .Error e => (e, "")) == ("op", "nop")

/-! The back-end pipeline.  The register allocator is an untrusted
    parameter; with a stub allocator the pipeline runs every RTL pass and
    stops at register allocation with the allocator's error. -/

def cfg : Compiler.Config :=
  { firstUnusedIdent := fun _ => P 1000
    compileSwitch := fun _ _ _ => .CTaction 0
    regalloc := fun _ => .Error "no register allocator"
    enumerateAux := fun _ _ => [] }

def prog (code : RTL.Code) (entry : Nat) : RTL.Program :=
  { prog_defs := [(P 10, .Gfun (.Internal (mkFun code entry)))],
    prog_public := [P 10], prog_main := P 10 }

#guard (match Compiler.transfRtlProgram cfg (prog dcCode 4) with
  | .OK _ => false
  | .Error e => e.endsWith "no register allocator")

-- A program without functions goes through the whole back end.
#guard (match Compiler.transfRtlProgram cfg { prog_defs := [], prog_public := [], prog_main := P 1 } with
  | .OK p => p.prog_defs.length == 0
  | .Error _ => false)

end OptimCheck
