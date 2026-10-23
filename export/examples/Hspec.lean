/-
  A small test framework in the style of Haskell's `hspec`: a test suite is a
  tree of `describe` groups and `it` examples, built in a `do` block and run by
  `hspec` from the `main` function of a test executable.

    def main (args : List String) : IO UInt32 := Hspec.hspec args do
      describe "addition" do
        it "is commutative" do
          shouldBe (1 + 2) (2 + 1)
        xit "a pending example" (pure ())

  Every example is an `IO Unit` action; it fails when it throws (the
  expectations `shouldBe`, `shouldSatisfy`, `shouldContain`, … throw an
  `IO.userError` describing the mismatch).  `hspec` prints the tree of results
  (`✔`/`✘`), the failures with their messages, the summary
  `N examples, M failures` and the elapsed time, and returns the exit code
  (0 iff no example failed).

  Command line (as `hspec`): `-m PATTERN` / `--match PATTERN` runs only the
  examples whose path (`group/subgroup/example`) contains `PATTERN` (the option
  can be repeated), `--skip PATTERN` skips them.

  Examples can be given a time limit with `withTimeout ms`: the example runs in
  a dedicated thread, and fails when it has not finished after `ms`
  milliseconds (the thread is then cancelled; long-running code can poll
  `IO.checkCanceled` to stop early).
-/
module

public section

namespace Hspec

/-- A test suite: a tree of groups and examples. -/
inductive SpecTree where
  /-- `describe name children` -/
  | group (name : String) (children : Array SpecTree)
  /-- `it name action`, with an optional time limit (milliseconds) -/
  | example (name : String) (action : IO Unit) (timeoutMs : Option Nat)
  /-- `xit name`: a pending example -/
  | pending (name : String) (reason : String)

/-- The monad in which test suites are written. -/
abbrev SpecM := StateM (Array SpecTree)

/-- A test suite. -/
abbrev Spec := SpecM Unit

/-- The trees built by a suite. -/
def Spec.trees (s : Spec) : Array SpecTree := (s.run #[]).2

/-- A group of examples. -/
def describe (name : String) (body : Spec) : Spec :=
  modify (·.push (.group name body.trees))

/-- Synonym of `describe`. -/
def context (name : String) (body : Spec) : Spec := describe name body

/-- An example. -/
def it (name : String) (action : IO Unit) : Spec :=
  modify (·.push (.example name action none))

/-- A pending example (not run). -/
def xit (name : String) (_action : IO Unit) (reason : String := "") : Spec :=
  modify (·.push (.pending name reason))

/-- Give a time limit (milliseconds) to the examples of `body` that have
    none. -/
def withTimeout (ms : Nat) (body : Spec) : Spec :=
  let rec go : SpecTree → SpecTree
    | .group n cs => .group n (cs.map go)
    | .example n a none => .example n a (some ms)
    | t => t
  modify (· ++ body.trees.map go)

/-! ## Expectations -/

/-- Fail the current example. -/
def expectationFailure {α : Type} (msg : String) : IO α :=
  throw (IO.userError msg)

/-- `actual` equals `expected`. -/
def shouldBe {α : Type} [BEq α] [Repr α] (actual expected : α) : IO Unit := do
  unless actual == expected do
    expectationFailure s!"expected: {reprStr expected}\n but got: {reprStr actual}"

/-- `actual` differs from `unexpected`. -/
def shouldNotBe {α : Type} [BEq α] [Repr α] (actual unexpected : α) : IO Unit := do
  if actual == unexpected then
    expectationFailure s!"not expected: {reprStr actual}"

/-- `actual` satisfies `p`. -/
def shouldSatisfy {α : Type} [Repr α] (actual : α) (p : α → Bool) : IO Unit := do
  unless p actual do
    expectationFailure s!"predicate failed on: {reprStr actual}"

/-- `actual` contains the substring `needle`. -/
def shouldContain (actual needle : String) : IO Unit := do
  unless (actual.splitOn needle).length > 1 do
    expectationFailure s!"{reprStr actual}\n does not contain {reprStr needle}"

/-- `actual` does not contain the substring `needle`. -/
def shouldNotContain (actual needle : String) : IO Unit := do
  if (actual.splitOn needle).length > 1 then
    expectationFailure s!"{reprStr actual}\n contains {reprStr needle}"

/-- The action throws an error. -/
def shouldThrow {α : Type} (action : IO α) : IO Unit := do
  let r ← action.toBaseIO
  if let .ok _ := r then expectationFailure "did not throw"

/-! ## Running a suite -/

/-- The options of the command line. -/
structure Options where
  patterns : List String := []
  skips : List String := []

/-- Parse the command line (`-m`/`--match`, `--skip`). -/
def parseArgs : List String → Except String Options
  | [] => .ok {}
  | "-m" :: p :: rest | "--match" :: p :: rest => do
    let o ← parseArgs rest; pure { o with patterns := p :: o.patterns }
  | "--skip" :: p :: rest => do
    let o ← parseArgs rest; pure { o with skips := p :: o.skips }
  | a :: _ => .error s!"unknown argument: {a}\nusage: [-m|--match PATTERN]… [--skip PATTERN]…"

private def contains (s pat : String) : Bool := (s.splitOn pat).length > 1

/-- Whether the example of path `path` is selected. -/
def Options.selects (o : Options) (path : String) : Bool :=
  (o.patterns.isEmpty || o.patterns.any (contains path ·)) && !o.skips.any (contains path ·)

/-- Whether a tree has a selected example. -/
partial def SpecTree.hasSelected (o : Options) (prefix_ : String) : SpecTree → Bool
  | .group n cs => cs.any (·.hasSelected o (prefix_ ++ n ++ "/"))
  | .example n _ _ | .pending n _ => o.selects (prefix_ ++ n)

/-- The results of a run. -/
structure Summary where
  examples : Nat := 0
  failures : Array (String × String) := #[]
  pending : Nat := 0

private def seconds (ms : Nat) : String :=
  let cs := ms / 10
  s!"{cs / 100}.{if cs % 100 < 10 then "0" else ""}{cs % 100}s"

/-- Run an action with an optional time limit. -/
partial def runWithTimeout (action : IO Unit) : Option Nat → IO (Except String Unit)
  | none => do
    match ← action.toBaseIO with
    | .ok () => pure (.ok ())
    | .error e => pure (.error (toString e))
  | some ms => do
    let t ← IO.asTask action .dedicated
    let start ← IO.monoMsNow
    let rec wait : IO (Except String Unit) := do
      if ← IO.hasFinished t then
        match t.get with
        | .ok () => pure (.ok ())
        | .error e => pure (.error (toString e))
      else if (← IO.monoMsNow) - start ≥ ms then
        IO.cancel t
        pure (.error s!"timed out after {seconds ms}")
      else
        IO.sleep 10
        wait
    wait

private def indent (depth : Nat) : String := String.ofList (List.replicate (2 * depth) ' ')

/-- Run the trees, printing the results. -/
partial def runTrees (o : Options) (depth : Nat) (prefix_ : String) (ts : Array SpecTree)
    (s : Summary) : IO Summary := do
  let mut s := s
  for t in ts do
    if !t.hasSelected o prefix_ then continue
    match t with
    | .group n cs =>
      IO.println s!"{indent depth}{n}"
      s ← runTrees o (depth + 1) (prefix_ ++ n ++ "/") cs s
    | .pending n reason =>
      IO.println s!"{indent depth}{n} [pending]{if reason.isEmpty then "" else s!" ({reason})"}"
      s := { s with pending := s.pending + 1 }
    | .example n action timeout =>
      let start ← IO.monoMsNow
      let r ← runWithTimeout action timeout
      let time := seconds ((← IO.monoMsNow) - start)
      s := { s with examples := s.examples + 1 }
      match r with
      | .ok () => IO.println s!"{indent depth}{n} [✔] ({time})"
      | .error msg =>
        s := { s with failures := s.failures.push (prefix_ ++ n, msg) }
        IO.println s!"{indent depth}{n} [✘] ({time})"
    (← IO.getStdout).flush
  return s

/-- Run a test suite with the given command line; the exit code is 0 iff
    every selected example passed. -/
def hspec (args : List String) (spec : Spec) : IO UInt32 := do
  let o ← match parseArgs args with
    | .ok o => pure o
    | .error msg => do IO.eprintln msg; return 2
  let start ← IO.monoMsNow
  let s ← runTrees o 0 "" spec.trees {}
  let time := seconds ((← IO.monoMsNow) - start)
  unless s.failures.isEmpty do
    IO.println "\nFailures:"
    for h : i in [0:s.failures.size] do
      let (path, msg) := s.failures[i]
      IO.println s!"\n  {i + 1}) {path}"
      for l in msg.splitOn "\n" do IO.println s!"       {l}"
  IO.println s!"\nFinished in {time}"
  let plural (n : Nat) (w : String) := s!"{n} {w}{if n == 1 then "" else "s"}"
  IO.println (s!"{plural s.examples "example"}, {plural s.failures.size "failure"}" ++
    (if s.pending > 0 then s!", {s.pending} pending" else ""))
  return if s.failures.isEmpty then 0 else 1

end Hspec

end
