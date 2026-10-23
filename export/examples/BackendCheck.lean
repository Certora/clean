/-
  Checks for the back-end passes ported in this round: instruction
  selection (`Selection`, `SelectOp`, `SelectLong`, `SelectDiv`), the
  liveness analysis (`Liveness`), the frame layout and `Stacking`
  (`Bounds`, `Stacklayout`, `Stacking`), `Debugvar` and the register
  allocation validator (`Allocation`) and inlining (`Inlining`).
  All facts are checked by `decide`.
-/
import CCLib.backend.Selection
import CCLib.backend.Liveness
import CCLib.backend.Stacking
import CCLib.backend.Debugvar
import CCLib.backend.Unusedglob
import CCLib.backend.Allocation
import CCLib.backend.Inlining

open CC CC.Op

namespace BackendCheck

def x : Ident := Positive.ofNat 1

/-! ## Instruction selection -/

def opts : Selection.Options := { compileSwitch := fun _ dfl _ => .CTaction dfl }

/-- `x + 1` is selected as an immediate addition. -/
example : (match Selection.selExpr opts
      (.Ebinop .Oadd (.Evar x) (.Econst (.Ointconst (Integers.Int.repr 1)))) with
    | .Eop (.Oaddimm n) (.Econs (.Evar y) .Enil) => n == Integers.Int.repr 1 && y == x
    | _ => false) = true := by decide

/-- `x * 8` is selected as a left shift by 3. -/
example : (match Selection.selExpr opts
      (.Ebinop .Omul (.Evar x) (.Econst (.Ointconst (Integers.Int.repr 8)))) with
    | .Eop (.Oshift .Slsl a) (.Econs (.Evar _) .Enil) => a.a32_amount == Integers.Int.repr 3
    | _ => false) = true := by decide

/-- `x / 7` (signed) is selected as a multiplication by the magic number
    `0x92492493` followed by shifts, inside a `let`. -/
example : (match Selection.selExpr opts
      (.Ebinop .Odiv (.Evar x) (.Econst (.Ointconst (Integers.Int.repr 7)))) with
    | .Elet (.Evar _) _ => true
    | _ => false) = true := by decide

/-- With `optim_for_size`, the division is kept. -/
example : (match Selection.selExpr { opts with optimForSize := true }
      (.Ebinop .Odiv (.Evar x) (.Econst (.Ointconst (Integers.Int.repr 7)))) with
    | .Eop .Odiv _ => true
    | _ => false) = true := by decide

/-- The magic numbers for signed division by 7 and unsigned division by 10. -/
example : SelectDiv.divsMulParams 7 = some (2, 2454267027) := by decide
example : SelectDiv.divuMulParams 10 = some (3, 3435973837) := by decide

/-- Floating-point division by 2.0 becomes a multiplication by 0.5. -/
example : (Floats.Float.exactInverse ⟨BitVec.ofNat 64 0x4000000000000000⟩).map (·.bits.toNat) =
    some 0x3FE0000000000000 := by decide

/-! ## Liveness -/

/-- `f(x) { y = x + 1; return y; }` in RTL: node 3 is the addition, node 2
    the return, node 1 is unused code. -/
def rtlFn : RTL.Function :=
  { fn_sig := mksignature [.Xint] .Xint cc_default, fn_params := [x], fn_stacksize := 0,
    fn_code := (PTree.empty.set (Positive.ofNat 3)
        (.Iop (.Oaddimm (Integers.Int.repr 1)) [x] (Positive.ofNat 2) (Positive.ofNat 2))).set
        (Positive.ofNat 2) (.Ireturn (some (Positive.ofNat 2))),
    fn_entrypoint := Positive.ofNat 3 }

/-- As in Rocq, `analyze` returns the registers live *after* each node:
    register 2 is live after the addition, nothing after the return, and
    `x` is live before the addition (`transfer` at node 3). -/
example : (match Liveness.analyze rtlFn with
    | some live => (Regset.mem (Positive.ofNat 2) (live.get (Positive.ofNat 3)),
                    (live.get (Positive.ofNat 2)).isEmpty,
                    Regset.mem x (Liveness.transfer rtlFn (Positive.ofNat 3)
                      (live.get (Positive.ofNat 3))))
    | none => (false, false, false)) = (true, true, true) := by decide

/-! ## Stacking -/

/-- A Linear function that spills one register to a local slot and calls a
    function: it uses callee-save register `R19`, one local slot and no
    outgoing arguments. -/
def linFn : Linear.Function :=
  { fn_sig := mksignature [] .Xint cc_default, fn_stacksize := 8,
    fn_code := [.Lop (.Ointconst (Integers.Int.repr 0)) [] .R19,
                .Lsetstack .R19 .Local 0 .Tint,
                .Lgetstack .Local 0 .Tint .R0,
                .Lreturn] }

/-- The inferred bounds: `R19` is saved, one local word, no outgoing area. -/
example : ((Bounds.functionBounds .AAPCS64 linFn).used_callee_save,
    (Bounds.functionBounds .AAPCS64 linFn).bound_local,
    (Bounds.functionBounds .AAPCS64 linFn).bound_outgoing,
    (Bounds.functionBounds .AAPCS64 linFn).bound_stack_data) = ([.R19], 1, 0, 8) := by decide

/-- The frame: back link at 0, return address at 8, callee-saves at 16,
    locals at 24, stack data at 32, total size 48 (16-aligned). -/
example : (let fe := Stacklayout.makeEnv (Bounds.functionBounds .AAPCS64 linFn)
    (fe.fe_ofs_link, fe.fe_ofs_retaddr, fe.fe_ofs_callee_save, fe.fe_ofs_local,
     fe.fe_stack_data, fe.fe_size)) = (0, 8, 16, 24, 32, 48) := by decide

/-- `Stacking` succeeds; the Mach code saves `R19`, runs the body, restores
    `R19` before returning: 6 Mach instructions in all. -/
example : (match Stacking.transfFunction .AAPCS64 linFn with
    | .OK tf => (tf.fn_stacksize, tf.fn_code.length)
    | .Error _ => (0, 0)) = (48, 6) := by decide

/-! ## Debugvar -/

/-- Without debug annotations, `Debugvar` leaves the code unchanged. -/
example : (match Debugvar.transfFunction linFn with
    | .OK tf => tf.fn_code.length
    | .Error _ => 0) = 4 := by decide


/-! ## Register allocation validation -/

/-- A candidate LTL allocation of `rtlFn`: `x` is in `R0` (as the calling
    convention requires) and `y` in `r`; with `mv`, the block of the return
    first moves `R1` to `R0`. -/
def ltlFn (r : Mreg) (mv : Bool) : LTL.Function :=
  { fn_sig := mksignature [.Xint] .Xint cc_default, fn_stacksize := 0,
    fn_code := ((PTree.empty.set (Positive.ofNat 3)
        [.Lop (.Oaddimm (Integers.Int.repr 1)) [.R0] r, .Lbranch (Positive.ofNat 2)]).set
        (Positive.ofNat 2)
        (if mv then [.Lop .Omove [.R1] .R0, .Lreturn] else [.Lreturn])).set
        (Positive.ofNat 4) [.Lbranch (Positive.ofNat 3)],
    fn_entrypoint := Positive.ofNat 4 }

def allocEnv : RTLtyping.Regenv := fun _ => .Tint

/-- `y` in `R0`: accepted. -/
example : (Allocation.checkFunction .AAPCS64 rtlFn (ltlFn .R0 false) allocEnv).isOK = true := by
  decide
/-- `y` in `R1` but returned from `R0`: rejected. -/
example : (Allocation.checkFunction .AAPCS64 rtlFn (ltlFn .R1 false) allocEnv).isOK = false := by
  decide
/-- `y` in `R1`, moved to `R0` before the return: accepted. -/
example : (Allocation.checkFunction .AAPCS64 rtlFn (ltlFn .R1 true) allocEnv).isOK = true := by
  decide
/-- `y` in `R0`, then `R1` (garbage) moved over it: rejected. -/
example : (Allocation.checkFunction .AAPCS64 rtlFn (ltlFn .R0 true) allocEnv).isOK = false := by
  decide


/-! ## Inlining -/

def sigInt : Signature := mksignature [.Xint] .Xint cc_default

/-- `g(a) { b = a + 1; return b; }` -/
def gFn : RTL.Function :=
  { fn_sig := sigInt, fn_params := [Positive.ofNat 1], fn_stacksize := 0,
    fn_code := (PTree.empty.set (Positive.ofNat 2)
        (.Iop (.Oaddimm (Integers.Int.repr 1)) [Positive.ofNat 1] (Positive.ofNat 2)
          (Positive.ofNat 1))).set
        (Positive.ofNat 1) (.Ireturn (some (Positive.ofNat 2))),
    fn_entrypoint := Positive.ofNat 2 }

/-- `f(x) { y = callee(x); return y; }` -/
def callerFn (callee : Ident) : RTL.Function :=
  { fn_sig := sigInt, fn_params := [x], fn_stacksize := 0,
    fn_code := (PTree.empty.set (Positive.ofNat 2)
        (.Icall sigInt (.inr callee) [x] (Positive.ofNat 2) (Positive.ofNat 1))).set
        (Positive.ofNat 1) (.Ireturn (some (Positive.ofNat 2))),
    fn_entrypoint := Positive.ofNat 2 }

def gId : Ident := Positive.ofNat 7

def isCall : RTL.Instruction → Bool
  | .Icall .. => true
  | _ => false

def calls (r : Res RTL.Function) : Nat :=
  match r with
  | .OK f => ((PTree.elements f.fn_code).filter (fun p => isCall p.2)).length
  | .Error _ => 100

/-- Inlining `g` into `f`: the call becomes `nop; move x→a; b = a + 1;
    move b→y`, at nodes 2, 5, 4, 3 (node 1 is the return). -/
example : (match Inlining.transfFunction (PTree.empty.set gId gFn) (callerFn gId) with
    | .OK f => (calls (.OK f), (PTree.elements f.fn_code).length, f.fn_entrypoint.toNat)
    | .Error _ => (100, 0, 0)) = (0, 5, 2) := by decide

/-- Without `g` in the environment, the call stays. -/
example : calls (Inlining.transfFunction PTree.empty (callerFn gId)) = 1 := by decide

/-- A self-recursive `g ↦ f` is inlined once into itself, then the
    recursion stops: one call remains. -/
example : calls (Inlining.transfFunction (PTree.empty.set gId (callerFn gId)) (callerFn gId)) = 1 := by
  decide

end BackendCheck
