/-
  Runs the whole Lean compiler, Clight to AArch64 Asm, on the example
  programs, with the oracles of `CCLib/extraction/extraction.lean`
  (`Switchaux.compileSwitch`, `Regalloc.regalloc`,
  `Linearize.enumerateAuxDefault`).  The `#guard`s are evaluated when this
  file is built: every program must get through every pass, including the
  validators of register allocation, linearization and switch compilation.
-/
import CCLib.extraction.extraction
import CCLib.riscV.extractionMachdep
import CCLib.x86.extractionMachdep
import GenSwap
import GenMain
import GenFuncPtr
import GenGotoBack
import GenGotoLeave
import GenLocalVar
import GenOOB
import GenStruct
import GenStructCopy
import GenU16Loop

namespace ExtractionCheck
open CC

/-- Number of internal functions and total number of Asm instructions, or
    the compiler's error message. -/
def summary (p : Program) : Except String (Nat × Nat) :=
  match Extraction.transf_clight_program p with
  | .Error e => .error e
  | .OK tp =>
    let fs := tp.prog_defs.filterMap fun (_, gd) => match gd with
      | .Gfun (.Internal f) => some f
      | _ => none
    .ok (fs.length, (fs.map fun f => f.fn_code.length).sum)

/-- The program compiles and its internal functions are non-empty. -/
def compiles (p : Program) : Bool :=
  match summary p with
  | .ok (n, k) => n > 0 && k > n
  | .error _ => false

#guard compiles Swap.prog
#guard compiles Main.prog
#guard compiles Funcptr.prog
-- `Gotoback` and `Gotoleave` assign to a function parameter with `Sset`,
-- i.e. they treat it as a temporary (Clight with `function_entry2`).  The
-- compiler's input is Clight with `function_entry1`, so `SimplLocals`
-- rejects them, exactly as `SimplLocals.check_temp` does in Rocq.
#guard (summary Gotoback.prog matches .error "In function: bad temporary")
#guard (summary Gotoleave.prog matches .error "In function: bad temporary")
#guard compiles Localvar.prog
#guard compiles Oob.prog
#guard compiles Structs2.prog
#guard compiles Structcopy.prog
#guard compiles U16loop.prog

-- With the stub allocator of `examples/OptimCheck.lean`, compilation stops at
-- register allocation: the allocator is what makes the pipeline complete.
#guard match Compiler.transfClightProgram
    { Extraction.defaultConfig with regalloc := fun _ => .Error "no allocator" } Swap.prog with
  | .Error e => e.endsWith "no allocator"
  | .OK _ => false

-- An allocator that returns a wrong result is rejected by the validator.
#guard match Compiler.transfClightProgram
    { Extraction.defaultConfig with
      regalloc := fun f => do
        let tf ← Regalloc.regallocSpillAll .AAPCS64 f
        -- drop the parameter moves of the entry block
        .OK { tf with fn_code := tf.fn_code.set tf.fn_entrypoint [.Lbranch f.fn_entrypoint] } }
    Swap.prog with
  | .Error _ => true
  | .OK _ => false

/-! ### A CompCert C program through `transf_c_program`

```c
int main(void) {
  int i, x;
  x = 0;
  for (i = 0; i < 10; i++)
    switch (i) { case 8: x += 64; break; ... case 0: x += 0; break; default: break; }
  return x;
}
```
`SimplExpr` needs `firstUnusedIdent` for the temporary of `i++`; the dense
switch becomes a jump table through `Switchaux.compileSwitch`. -/

namespace CProg

def P (n : Nat) : Ident := Positive.ofNat n
def vi : Csyntax.Expr := .Evar (P 10) tint
def vx : Csyntax.Expr := .Evar (P 11) tint
def cst (k : Int) : Csyntax.Expr := .Eval (.Vint (Integers.Int.repr k)) tint

def cases : Nat → Csyntax.LStmts
  | 0 => .LScons none .Sbreak .LSnil
  | n + 1 => .LScons (some (n : Int))
      (.Ssequence (.Sdo (.Eassignop .Oadd vx (cst (n * n)) tint tint)) .Sbreak) (cases n)

def body : Csyntax.Stmt :=
  .Ssequence (.Sdo (.Eassign vx (cst 0) tint))
  (.Ssequence
    (.Sfor (.Sdo (.Eassign vi (cst 0) tint)) (.Ebinop .Olt (.Evalof vi tint) (cst 10) tint)
       (.Sdo (.Epostincr .Incr vi tint))
       (.Sswitch (.Evalof vi tint) (cases 9)))
    (.Sreturn (some (.Evalof vx tint))))

def mainFn : Csyntax.Function :=
  { fn_return := tint, fn_callconv := cc_default, fn_params := [],
    fn_vars := [(P 10, tint), (P 11, tint)], fn_body := body }

/-- The runtime support functions that the C front end declares in every
    program (`Selection` checks their declarations). -/
def runtimeDecls : List (Ident × GlobDef Csyntax.FunDef Ty) :=
  Swap.global_definitions.filterMap fun (id, gd) => match gd with
    | .Gfun (.External ef targs tres cc) => some (id, .Gfun (.External ef targs tres cc))
    | _ => none

def prog : Csyntax.Program :=
  { prog_defs := runtimeDecls ++ [(P 1, .Gfun (.Internal mainFn))], prog_public := [P 1],
    prog_main := P 1, prog_types := [], prog_comp_env := PTree.empty,
    prog_comp_env_eq := rfl }

/-- The Asm code of `main`. -/
def mainCode : Option Asm.Code :=
  match Extraction.transf_c_program prog with
  | .OK tp => match tp.prog_defs.lookup (P 1) with
    | some (.Gfun (.Internal f)) => some f.fn_code
    | _ => none
  | .Error _ => none

#guard mainCode.isSome
#guard (mainCode.getD []).any fun i => i matches .Pbtbl ..

end CProg

/-! ### Calls with stack arguments, division, shifts, floats

```c
int f(int a, int b, int c, int d, int e, int g, int h, int k, int l,
      double x, double y, double z, double u, double v, double w, double s,
      double t, double q) {
  return a / b + c % d + (e << g) + (h >> k) + l + (int)(x * y + z + u + v + w + s + t + q);
}
int main(void) { return f(100, 7, 50, 6, 1, 3, 64, 2, 9, 1.0, ..., 9.0); }
```
Nine integer and nine float arguments: some are passed on the stack on all
three targets, division and shifts use fixed registers on x86. -/

namespace Args

def P (n : Nat) : Ident := Positive.ofNat n
def ints : List Ident := (List.range 9).map fun i => P (20 + i)
def flts : List Ident := (List.range 9).map fun i => P (40 + i)
def iv (id : Ident) : Csyntax.Expr := .Evalof (.Evar id tint) tint
def fv (id : Ident) : Csyntax.Expr := .Evalof (.Evar id tdouble) tdouble
def bin (op : Binop) (a b : Csyntax.Expr) (ty : Ty := tint) : Csyntax.Expr := .Ebinop op a b ty
def ii (k : Nat) : Csyntax.Expr := iv (ints.getD k (P 1))
def ff (k : Nat) : Csyntax.Expr := fv (flts.getD k (P 1))

def fsum : Csyntax.Expr :=
  (List.range 7).foldl (fun e k => bin .Oadd e (ff (k + 2)) tdouble)
    (bin .Omul (ff 0) (ff 1) tdouble)

def fBody : Csyntax.Stmt :=
  .Sreturn (some
    (bin .Oadd
      (bin .Oadd (bin .Oadd (bin .Oadd (bin .Odiv (ii 0) (ii 1)) (bin .Omod (ii 2) (ii 3)))
        (bin .Oshl (ii 4) (ii 5))) (bin .Oshr (ii 6) (ii 7)))
      (bin .Oadd (ii 8) (.Ecast fsum tint))))

def fParams : List (Ident × Ty) := ints.map (·, tint) ++ flts.map (·, tdouble)

def fFn : Csyntax.Function :=
  { fn_return := tint, fn_callconv := cc_default, fn_params := fParams, fn_vars := [],
    fn_body := fBody }

def fTy : Ty := .Tfunction (fParams.map (·.2)) tint cc_default

def argList : List Csyntax.Expr :=
  ([100, 7, 50, 6, 1, 3, 64, 2, 9].map fun (n : Int) => .Eval (.Vint (Integers.Int.repr n)) tint) ++
  ((List.range 9).map fun k => .Eval (.Vfloat (Floats.Float.ofInt (Integers.Int.repr (k + 1)))) tdouble)

def mainFn : Csyntax.Function :=
  { fn_return := tint, fn_callconv := cc_default, fn_params := [], fn_vars := [],
    fn_body := .Sreturn (some (.Ecall (.Evar (P 2) fTy)
      (argList.foldr .Econs .Enil) tint)) }

def prog : Csyntax.Program :=
  { prog_defs := CProg.runtimeDecls ++
      [(P 2, .Gfun (.Internal fFn)), (P 1, .Gfun (.Internal mainFn))],
    prog_public := [P 1], prog_main := P 1, prog_types := [], prog_comp_env := PTree.empty,
    prog_comp_env_eq := rfl }

def ok {A : Type} : Res A → Bool
  | .OK _ => true
  | .Error _ => false

-- AArch64
#guard ok (Extraction.transf_c_program prog)
-- RISC-V (RV64)
#guard ok (RiscV.Compiler.transfCProgram RiscV.ExtractionMachdep.defaultConfig prog)
-- x86-64, System V and Windows conventions
#guard ok (X86.Compiler.transfCProgram X86.ExtractionMachdep.defaultConfig prog)
#guard ok (X86.Compiler.transfCProgram (X86.ExtractionMachdep.configFor { system := "cygwin" }) prog)
-- RISC-V and x86-64 on the Clight examples
#guard ok (RiscV.Compiler.transfClightProgram RiscV.ExtractionMachdep.defaultConfig Funcptr.prog)
#guard ok (X86.Compiler.transfClightProgram X86.ExtractionMachdep.defaultConfig Funcptr.prog)
#guard ok (X86.Compiler.transfClightProgram X86.ExtractionMachdep.defaultConfig Structcopy.prog)

-- With `f` declared `inline` (the `C2C` information given to
-- `Inliningaux`), `f` is inlined into `main` and then removed by `Unusedglob`.
def inlineF : Inliningaux.Options :=
  { atomInline := fun id => if id = P 2 then .Inline else .No_specifier }

#guard match Compiler.transfCProgram (Extraction.configFor {} inlineF) prog with
  | .OK tp => (tp.prog_defs.lookup (P 2)).isNone && (tp.prog_defs.lookup (P 1)).isSome
  | .Error _ => false

-- Without it, `f` stays.
#guard match Extraction.transf_c_program prog with
  | .OK tp => (tp.prog_defs.lookup (P 2)).isSome
  | .Error _ => false

end Args

end ExtractionCheck
