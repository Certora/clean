/-
  Checks of `CCLib.cfrontend.Initializers` (`cfrontend/Initializers.v`) by evaluation:
  translation of an array initializer with zero padding, of the address of a
  global, and of a struct with two bitfields sharing one 32-bit carrier
  (`load_int`/`store_int` through `trisection`).
-/
import CCLib.cfrontend.Initializers

open CC CC.Initializers

namespace InitializersCheck

def ce : CompositeEnv := PTree.empty

def cst (n : Int) : Initializer := .Init_single (.Eval (.Vint (Integers.Int.repr n)) type_int32s)

/-- `int x[3] = {1, 2};` -/
example : translInit ce (.Tarray type_int32s 3 noattr) (.Init_array (.Init_cons (cst 1) (.Init_cons (cst 2) .Init_nil))) =
    .OK [.Init_int32 (Integers.Int.repr 1), .Init_int32 (Integers.Int.repr 2), .Init_space 4] := by
  decide

/-- Too many elements for the array. -/
example : (translInit ce (.Tarray type_int32s 1 noattr)
    (.Init_array (.Init_cons (cst 1) (.Init_cons (cst 2) .Init_nil)))).isOK = false := by
  decide

/-- `int *p = &x;` -/
example : translInit ce (.Tpointer type_int32s noattr)
    (.Init_single (.Eaddrof (.Evar Positive.xH type_int32s) (.Tpointer type_int32s noattr))) =
    .OK [.Init_addrof Positive.xH Integers.Ptrofs.zero] := by
  decide

/-- `struct { unsigned a:3; unsigned b:5; int c; } s = {5, 7, 9};` — both
    bitfields live in the first 32-bit word: `5 + (7 << 3) = 61`. -/
def sdef : CompositeDef := .Composite .xH .Struct
  [.Member_bitfield (.xO .xH) .I32 .Unsigned noattr 3 false,
   .Member_bitfield (.xI .xH) .I32 .Unsigned noattr 5 false,
   .Member_plain (.xO (.xO .xH)) type_int32s] noattr

def ce2 : CompositeEnv :=
  match buildCompositeEnv [sdef] with
  | .OK ce => ce
  | .Error _ => PTree.empty

example : translInit ce2 (.Tstruct .xH noattr)
    (.Init_struct (.Init_cons (cst 5) (.Init_cons (cst 7) (.Init_cons (cst 9) .Init_nil)))) =
    .OK [.Init_int32 (Integers.Int.repr 61), .Init_int32 (Integers.Int.repr 9)] := by
  decide

end InitializersCheck
