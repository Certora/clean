/-
  Tests of the reference interpreter (`ccomp -interp`, `CCLib.driver.Interp`),
  written as an `IO` test suite in the style of `hspec` and run by the `main`
  function of the executable `interpspec` (`lake test`, or
  `lake exe interpspec [-m PATTERN]`).

  Every example writes a small C program to a temporary directory, runs the
  driver `CC.Driver.main` with `-interp` on it in-process (compiled code, not
  the `#eval` evaluator), captures what the run prints, and checks the output
  and the exit code.

  The `-all` examples explore every evaluation order.  In the loop example
  every iteration evaluates `f(i) * f(s)`; both orders of the two calls give the
  same result, but the freed stack frames of the two calls keep different
  contents (`Mem.free` only removes permissions), and states are compared with
  their whole memory contents, as `compare_mem` in `driver/Interp.ml` does.  So
  the number of distinct states doubles at every iteration, and the run ends
  with `2^(n-2)` final states for `n` iterations (`n ≥ 2`).  This growth comes
  from the semantics and the state comparison of the OCaml interpreter, which
  the port follows; the example checks it and bounds the run with a time
  limit.
-/
import CCLib.driver.Driver
import Hspec

open Hspec

namespace InterpSpec

/-- The result of a run of the interpreter. -/
structure Run where
  /-- what the run printed (standard output and standard error) -/
  output : String
  exitCode : UInt32

/-- The lines of the output. -/
def Run.lines (r : Run) : List String := r.output.splitOn "\n"

/-- The number of lines of the output equal to `l`. -/
def Run.count (r : Run) (l : String) : Nat := (r.lines.filter (· == l)).length

/-- Run `ccomp -interp opts prog.c` on the C source `src`. -/
def interp (opts : List String) (src : String) : IO Run := do
  let dir ← IO.FS.createTempDir
  try
    let file := dir / "prog.c"
    IO.FS.writeFile file src
    let args := ["-interp"] ++ opts ++ [file.toString]
    let (out, code) ← IO.FS.withIsolatedStreams
      (CC.Driver.main CC.Driver.aarch64Target "ccomp" args CC.Driver.aarch64_linux)
    return { output := out, exitCode := code }
  finally
    IO.FS.removeDirAll dir

/-- `printf` is declared by hand: the configuration has no standard headers. -/
def stdio : String := "int printf(const char *, ...);\n"

def factorial : String := stdio ++ "
int fact(int n) { return n <= 1 ? 1 : n * fact(n - 1); }
int main(void) {
  printf(\"%d\\n\", fact(10));
  return fact(5) % 256;
}
"

def controlFlow : String := stdio ++ "
int classify(int x) {
  switch (x % 4) {
  case 0: return 10;
  case 1:
  case 2: return 20;
  default: break;
  }
  return 30;
}
int main(void) {
  int s = 0, i = 0;
  while (i < 8) { s += classify(i); i++; }
  for (i = 0; i < 3; i++) { if (i == 1) continue; s += 100; }
  do { s--; } while (s % 7 != 0);
  i = 0;
again:
  i++;
  if (i < 5) goto again;
  printf(\"%d %d\\n\", s, i);
  return 0;
}
"

def structs : String := stdio ++ "
struct point { int x; int y; };
struct point mk(int x, int y) { struct point p; p.x = x; p.y = y; return p; }
int dot(struct point a, struct point b) { return a.x * b.x + a.y * b.y; }
int main(void) {
  struct point p = mk(3, 4), q;
  q = p;
  q.y = 5;
  printf(\"%d\\n\", dot(p, q));
  return 0;
}
"

def heap : String := stdio ++ "
void *malloc(unsigned long);
void free(void *);
int main(void) {
  int *a = malloc(5 * sizeof(int));
  int i, s = 0;
  for (i = 0; i < 5; i++) a[i] = i * i;
  for (i = 0; i < 5; i++) s += a[i];
  free(a);
  printf(\"%d\\n\", s);
  return 0;
}
"

def volatiles : String := "
volatile int v;
int main(void) {
  v = 42;
  return v + 1;
}
"

def formats : String := stdio ++ "
int main(void) {
  printf(\"[%5d|%-4x|%04u|%c|%s|%%]\\n\", 42, 255, 7u, 'z', \"str\");
  printf(\"[%lld|%llx]\\n\", -5LL, 255LL);
  printf(\"[%f|%.2e|%g]\\n\", 1.5, 12345.678, 0.0001);
  return 0;
}
"

def outOfBounds : String := "
int main(void) {
  int a[2] = {1, 2};
  int i = 5;
  return a[i];
}
"

def mainArgs : String := "
int main(int argc, char **argv) { return argc + 3; }
"

def voidMain : String := stdio ++ "
void main(void) { printf(\"hello\\n\"); }
"

def endless : String := "
int main(void) { for (;;) { } }
"

/-- An unspecified evaluation order with two different results. -/
def unspecifiedOrder : String := "
int x;
int f(void) { x = 1; return 1; }
int g(void) { x = 2; return 2; }
int main(void) { int r = f() + g(); return x; }
"

/-- A loop of `n` iterations, each evaluating two calls in an unspecified
    order (same result, different freed stack frames). -/
def callLoop (n : Nat) : String := stdio ++ s!"
int f(int x) \{ return x + 1; }
int main(void) \{
  int s = 0;
  for (int i = 0; i < {n}; i++) s += f(i) * f(s);
  printf(\"%d\\n\", s);
  return s % 7;
}
"

/-- The result of `callLoop n`: `s ↦ s + (i + 1) * (s + 1)`, from `s = 0`. -/
def callLoopResult (n : Nat) : Int := Id.run do
  let mut s : Int := 0
  for i in [0:n] do s := s + (i + 1) * (s + 1)
  return s

def spec : Spec := do
  describe "ccomp -interp" do
    describe "one execution" do
      it "runs a recursive function and returns its exit code" do
        let r ← interp ["-quiet"] factorial
        shouldBe r.output "3628800\n"
        shouldBe r.exitCode 120
      it "runs while, for, do-while, switch and goto" do
        let r ← interp ["-quiet"] controlFlow
        shouldBe r.output "357 5\n"
        shouldBe r.exitCode 0
      it "passes, returns and copies structs (-fstruct-passing)" do
        let r ← interp ["-quiet", "-fstruct-passing"] structs
        shouldBe r.output "29\n"
      it "allocates and frees memory with malloc and free" do
        let r ← interp ["-quiet"] heap
        shouldBe r.output "30\n"
      it "reports volatile accesses as observable events" do
        let r ← interp [] volatiles
        shouldContain r.output "volatile store int32[&v+0] <- 42"
        shouldContain r.output "volatile load int32[&v+0] -> 42"
        shouldContain r.output "program terminated (exit code = 43)"
        shouldBe r.exitCode 43
      it "emulates printf conversions" do
        let r ← interp ["-quiet"] formats
        shouldBe r.output
          "[   42|ff  |0007|z|str|%]\n[-5|ff]\n[1.500000|1.23e+04|0.0001]\n"
      it "stops with exit code 126 on undefined behaviour" do
        let r ← interp ["-quiet"] outOfBounds
        shouldContain r.output "Stuck state"
        shouldContain r.output "ERROR: Undefined behavior"
        shouldBe r.exitCode 126
      it "calls main(argc, argv) with argc = 0" do
        let r ← interp ["-quiet"] mainArgs
        shouldBe r.exitCode 3
      it "calls a main returning void and exits with 0" do
        let r ← interp ["-quiet"] voidMain
        shouldContain r.output "warning: return type of 'main' should be 'int'"
        shouldSatisfy r.output (·.endsWith "\nhello\n")
        shouldBe r.exitCode 0
      it "is stopped by the time limit of an example when it does not terminate" do
        let r ← runWithTimeout (discard (interp ["-quiet"] endless)) (some 1000)
        match r with
        | .error msg => shouldContain msg "timed out"
        | .ok () => expectationFailure "the endless program terminated"
    describe "-random" do
      it "gives the result of the program when it does not depend on the order" do
        let r ← interp ["-quiet", "-random"] factorial
        shouldBe r.output "3628800\n"
        shouldBe r.exitCode 120
    describe "-all" do
      it "finds both results of an unspecified evaluation order" do
        let r ← interp ["-all"] unspecifiedOrder
        shouldBe (r.count "Time 39: program terminated (exit code = 1)") 1
        shouldBe (r.count "Time 39: program terminated (exit code = 2)") 1
        shouldBe r.exitCode 0
      withTimeout 120000 do
        it "explores 4 iterations of two unordered calls: 4 final states" do
          let r ← interp ["-all"] (callLoop 4)
          shouldBe (r.count s!"{callLoopResult 4}") 4
          shouldBe (r.count "Time 215: program terminated (exit code = 0)") 4
      withTimeout 300000 do
        it "explores 10 iterations of two unordered calls (~485 steps): 256 final states" do
          let r ← interp ["-all"] (callLoop 10)
          shouldBe (callLoopResult 10) 39916799
          shouldBe (r.count "39916799") 256
          shouldBe (r.count "Time 485: program terminated (exit code = 6)") 256
          shouldBe r.exitCode 0

end InterpSpec

def main (args : List String) : IO UInt32 := hspec args InterpSpec.spec
