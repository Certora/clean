/-
  Port of `cparser/Cflow.ml`: a simple control flow analysis for C
  statements.  Main purpose: emit warnings for non-void functions that fall
  through, and for `_Noreturn` functions that can return.

  Statements are abstracted as "flow transformers", functions from possible
  inputs to possible outcomes.  Because the test of a condition evaluates a
  constant expression (`Ceval.integer_expr`, which reads the machine
  configuration), a flow is a function `Inflow → M Outflow`.
-/
import CCLib.cparser.Ceval

namespace CC
namespace CParser
namespace Cflow

open C Cutil

abbrev StringSet := Std.HashSet String

/-- Functions declared noreturn by the standard, plus
    `__builtin_unreachable`. -/
def std_noreturn_functions : List String :=
  ["longjmp", "exit", "_exit", "abort", "_Exit", "quick_exit", "thrd_exit",
   "__builtin_unreachable"]

structure Inflow where
  /-- start normally at beginning of statement -/
  inormal : Bool
  /-- start at any "case" or "default" label -/
  iswitch : Bool
  /-- start at one of the goto labels in the set -/
  igoto : StringSet

structure Outflow where
  /-- terminates normally by falling through -/
  onormal : Bool
  /-- terminates early by "break" -/
  obreak : Bool
  /-- terminates early by "continue" -/
  ocontinue : Bool
  /-- terminates early by "return" -/
  oreturn : Bool
  /-- terminates early by "goto" to one of the labels in the set -/
  ogoto : StringSet

abbrev Flow := Inflow → M Outflow

def union (a b : StringSet) : StringSet := b.fold (fun s x => s.insert x) a

def subset (a b : StringSet) : Bool := a.toList.all b.contains

/-- The l.u.b. of two out flows -/
def join (o1 o2 : Outflow) : Outflow :=
  { onormal := o1.onormal || o2.onormal, obreak := o1.obreak || o2.obreak,
    ocontinue := o1.ocontinue || o2.ocontinue, oreturn := o1.oreturn || o2.oreturn,
    ogoto := union o1.ogoto o2.ogoto }

private def none_ : Outflow :=
  { onormal := false, obreak := false, ocontinue := false, oreturn := false, ogoto := {} }

/-! Some elementary flows -/

def normal : Flow := fun i => pure { none_ with onormal := i.inormal }
def break_ : Flow := fun i => pure { none_ with obreak := i.inormal }
def continue_ : Flow := fun i => pure { none_ with ocontinue := i.inormal }
def return_ : Flow := fun i => pure { none_ with oreturn := i.inormal }
def goto (lbl : String) : Flow := fun i =>
  pure { none_ with ogoto := if i.inormal then ({} : StringSet).insert lbl else {} }
def noflow : Flow := fun _ => pure none_

/-! Some flow transformers -/

/-- Sequential composition -/
def seq (s1 s2 : Flow) : Flow := fun i => do
  let o1 ← s1 i
  let o2 ← s2 { i with inormal := o1.onormal }
  return { onormal := o2.onormal, obreak := o1.obreak || o2.obreak,
           ocontinue := o1.ocontinue || o2.ocontinue, oreturn := o1.oreturn || o2.oreturn,
           ogoto := union o1.ogoto o2.ogoto }

/-- Nondeterministic choice -/
def either (s1 s2 : Flow) : Flow := fun i => do return join (← s1 i) (← s2 i)

/-- Is a condition always true or always false? -/
def resolve_test (env : Env.T) (e : Exp) : M (Option Bool) :=
  tryCatch (do
    match ← Ceval.integer_expr env e with
    | none => return none
    | some n => return some (n != 0)) fun
    | .EnvError _ => pure none
    | ex => throw ex

/-- If-then-else, with special cases for conditions that are always true or
    always false. -/
def if_ (env : Env.T) (e : Exp) (s1 s2 : Flow) : Flow := fun i => do
  match ← resolve_test env e with
  | some true => s1 i
  | some false => s2 i
  | none => either s1 s2 i

/-- Convert "continue" into "fallthrough". -/
def catch_continue (s : Flow) : Flow := fun i => do
  let o ← s i
  return { o with onormal := o.onormal || o.ocontinue, ocontinue := false }

/-- Convert "break" into "fallthrough". -/
def catch_break (s : Flow) : Flow := fun i => do
  let o ← s i
  return { o with onormal := o.onormal || o.obreak, obreak := false }

/-- Statements labeled with a goto label -/
def label (lbl : String) (s : Flow) : Flow := fun i =>
  s { i with inormal := i.inormal || i.igoto.contains lbl }

def case (s : Flow) : Flow := fun i => s { i with inormal := i.inormal || i.iswitch }

def switch (s : Flow) : Flow := fun i => s { i with inormal := false, iswitch := i.inormal }

/-- The flow for an infinite loop with body `s`. -/
def loop (s : Flow) : Flow := fun i => do
  let o ← s i
  if o.onormal && !i.inormal then s { i with inormal := true }
  else return { o with onormal := false }

/-- Detect the presence of a 'default' case reachable from an enclosing
    'switch' -/
partial def contains_default (s : Stmt) : Bool :=
  match s.sdesc with
  | .Sseq s1 s2 | .Sif _ s1 s2 => contains_default s1 || contains_default s2
  | .Swhile _ s | .Sdowhile s _ => contains_default s
  | .Sfor s1 _ s2 s3 => contains_default s1 || contains_default s2 || contains_default s3
  | .Sswitch _ _ => false
  | .Slabeled .Sdefault _ => true
  | .Slabeled _ s => contains_default s
  | .Sblock sl => sl.any contains_default
  | _ => false

/-- Extract the attributes of a function type, looking for "noreturn". -/
partial def function_attributes (env : Env.T) : Typ → M Attributes
  | .TFun _ _ _ a => pure a
  | .TPtr t _ => function_attributes env t
  | t@(.TNamed ..) =>
      tryCatch (do function_attributes env (← unroll env t)) fun
        | .EnvError _ => pure []
        | ex => throw ex
  | _ => pure []

mutual
/-- Given a C statement `s`, a flow that overapproximates its behavior. -/
partial def outcomes (env : Env.T) (s : Stmt) : Flow := fun i => do
  match s.sdesc with
  | .Sskip => normal i
  | .Sdo (.mk (.ECall fn _) _) =>
      let attr_noreturn :=
        find_custom_attributes ["noreturn", "__noreturn__"] (← function_attributes env fn.etyp)
      let std_noreturn := std_noreturn_functions.any (is_call_to_fun fn)
      if !attr_noreturn.isEmpty || std_noreturn then noflow i else normal i
  | .Sdo _ => normal i
  | .Sseq s1 s2 => seq (outcomes env s1) (outcomes env s2) i
  | .Sif e s1 s2 => if_ env e (outcomes env s1) (outcomes env s2) i
  | .Swhile e s =>
      catch_break (loop (if_ env e (catch_continue (outcomes env s)) break_)) i
  | .Sdowhile s e =>
      catch_break (loop (seq (catch_continue (outcomes env s)) (if_ env e normal break_))) i
  | .Sfor s1 e s2 s3 =>
      seq (outcomes env s1)
        (catch_break (loop (if_ env e
          (seq (catch_continue (outcomes env s2)) (outcomes env s3)) break_))) i
  | .Sbreak => break_ i
  | .Scontinue => continue_ i
  | .Sswitch _ s =>
      let fl := catch_break (switch (outcomes env s))
      if contains_default s then fl i else either normal fl i
  | .Slabeled (.Slabel lbl) s => label lbl (outcomes env s) i
  | .Slabeled _ s => case (outcomes env s) i
  | .Sgoto lbl => goto lbl i
  | .Sreturn _ => return_ i
  | .Sblock sl => outcomes_block env sl i
  | .Sdecl _ | .Sasm .. => normal i

partial def outcomes_block (env : Env.T) : List Stmt → Flow
  | [] => normal
  | s1 :: sl => seq (outcomes env s1) (outcomes_block env sl)
end

/-- Given the body of a function, estimate if and how this function can
    return: (can return, can return by fall-through). -/
partial def function_returns (env : Env.T) (body : Stmt) : M (Bool × Bool) := do
  let rec fixpoint (i : Inflow) : M Outflow := do
    let o ← outcomes env body i
    if subset o.ogoto i.igoto then return o
    else fixpoint { i with igoto := union i.igoto o.ogoto }
  let o ← fixpoint { inormal := true, iswitch := false, igoto := {} }
  return (o.onormal || o.oreturn, o.onormal)

end Cflow
end CParser
end CC
