/-
  The test programs of the assembly printers (`X86AsmCheck.lean`,
  `AArch64AsmCheck.lean`, `test/x86asm/run.sh`): the Clight examples
  (`clightgen -lean` output) and two CompCert C programs.
-/
import CCLib.cfrontend.Csyntax
import GenSwap
import GenMain
import GenFuncPtr
import GenLocalVar
import GenOOB
import GenStruct
import GenStructCopy
import GenU16Loop
import lean.demo

namespace AsmTestPrograms
open CC

/-! ## Two CompCert C programs

The same programs as in `examples/ExtractionCheck.lean`, with identifiers
built from names (`identOfString`), so that the symbols `main` and `f` of the
assembly file are the C names. -/

/-- The runtime support functions declared by the C front end. -/
def runtimeDecls : List (Ident × GlobDef Csyntax.FunDef Ty) :=
  Swap.global_definitions.filterMap fun (id, gd) => match gd with
    | .Gfun (.External ef targs tres cc) => some (id, .Gfun (.External ef targs tres cc))
    | _ => none

def cst (k : Int) : Csyntax.Expr := .Eval (.Vint (Integers.Int.repr k)) tint

namespace CSwitch

/-!
```c
int main(void) {
  int i, x;
  x = 0;
  for (i = 0; i < 10; i++)
    switch (i) { case 8: x += 64; break; ... case 0: x += 0; break; default: break; }
  return x;   /* 204 */
}
```
-/

def vi : Csyntax.Expr := .Evar (identOfString "i") tint
def vx : Csyntax.Expr := .Evar (identOfString "x") tint

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
    fn_vars := [(identOfString "i", tint), (identOfString "x", tint)], fn_body := body }

def prog : Csyntax.Program :=
  { prog_defs := runtimeDecls ++ [(identOfString "main", .Gfun (.Internal mainFn))],
    prog_public := [identOfString "main"], prog_main := identOfString "main", prog_types := [],
    prog_comp_env := PTree.empty, prog_comp_env_eq := rfl }

end CSwitch

namespace Args

/-!
```c
int f(int a, int b, int c, int d, int e, int g, int h, int k, int l,
      double x, double y, double z, double u, double v, double w, double s,
      double t, double q) {
  return a / b + c % d + (e << g) + (h >> k) + l + (int)(x * y + z + u + v + w + s + t + q);
}
int main(void) { return f(100, 7, 50, 6, 1, 3, 64, 2, 9, 1.0, ..., 9.0); }   /* 93 */
```
-/

def ints : List Ident := (List.range 9).map fun i => identOfString s!"a{i}"
def flts : List Ident := (List.range 9).map fun i => identOfString s!"x{i}"
def iv (id : Ident) : Csyntax.Expr := .Evalof (.Evar id tint) tint
def fv (id : Ident) : Csyntax.Expr := .Evalof (.Evar id tdouble) tdouble
def bin (op : Binop) (a b : Csyntax.Expr) (ty : Ty := tint) : Csyntax.Expr := .Ebinop op a b ty
def ii (k : Nat) : Csyntax.Expr := iv (ints.getD k (identOfString "?"))
def ff (k : Nat) : Csyntax.Expr := fv (flts.getD k (identOfString "?"))

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
    fn_body := .Sreturn (some (.Ecall (.Evar (identOfString "f") fTy)
      (argList.foldr .Econs .Enil) tint)) }

def prog : Csyntax.Program :=
  { prog_defs := runtimeDecls ++
      [(identOfString "f", .Gfun (.Internal fFn)), (identOfString "main", .Gfun (.Internal mainFn))],
    prog_public := [identOfString "f", identOfString "main"], prog_main := identOfString "main",
    prog_types := [], prog_comp_env := PTree.empty, prog_comp_env_eq := rfl }

end Args

/-! ## The programs and their assembly text -/

/-- The Clight programs (`clightgen -lean` output), by C file name. -/
def clightPrograms : List (String × Program) :=
  [("swap", Swap.prog), ("main", Main.prog), ("funcptr", Funcptr.prog),
   ("localvar", Localvar.prog), ("oob", Oob.prog), ("structs2", Structs2.prog),
   ("structcopy", Structcopy.prog), ("u16loop", U16loop.prog), ("demo", Demo.prog)]

/-- The CompCert C programs. -/
def cPrograms : List (String × Csyntax.Program) :=
  [("switch", CSwitch.prog), ("args", Args.prog)]

end AsmTestPrograms
