/-
  Port of `cparser/SwitchNorm.ml`: normalization of structured `switch`
  statements and emulation of unstructured `switch` statements (e.g. Duff's
  device).  Assumes code without blocks; produces code without blocks and
  with normalized `switch` statements:
  `Sswitch(e, Sseq (Slabeled(lbl1, case1), Sseq (... Sseq (Slabeled(lblN,caseN), Sskip) ...)))`.

  The global references `support_unstructured` and `new_label` are the
  argument `unstructured` and the state of the monad `SM` (the label counter
  starts at 0 for each call of `program`).
-/
import CCLib.cparser.Cutil

namespace CC
namespace CParser
namespace SwitchNorm

open C Cutil

inductive SwitchLabel where
  | Case (e : Exp) (n : Int64)
  | Default
  deriving Inhabited

instance : BEq SwitchLabel where
  beq
    | .Case e1 n1, .Case e2 n2 => e1 == e2 && n1 == n2
    | .Default, .Default => true
    | _, _ => false

inductive SwitchBody where
  | Label (l : SwitchLabel) (loc : Location)
  | Stmt (s : C.Stmt)
  deriving Inhabited

partial def flatten_switch : List C.Stmt → List SwitchBody
  | [] => []
  | s :: rem =>
    match s.sdesc with
    | .Sseq s1 s2 => flatten_switch (s1 :: s2 :: rem)
    | .Slabeled (.Scase e n) s1 => .Label (.Case e n) s.sloc :: flatten_switch (s1 :: rem)
    | .Slabeled .Sdefault s1 => .Label .Default s.sloc :: flatten_switch (s1 :: rem)
    | .Slabeled (.Slabel lbl) s1 =>
        .Stmt (.mk (.Slabeled (.Slabel lbl) sskip) s.sloc) :: flatten_switch (s1 :: rem)
    | _ => .Stmt s :: flatten_switch rem

def group_switch : List SwitchBody → C.Stmt × List (SwitchLabel × Location × C.Stmt)
  | [] => (sskip, [])
  | .Label case loc :: rem =>
      let (fst, cases) := group_switch rem
      (sskip, (case, loc, fst) :: cases)
  | .Stmt s :: rem =>
      let (fst, cases) := group_switch rem
      (sseq s.sloc s fst, cases)

def label_of_switchlabel : SwitchLabel → SLabel
  | .Case e n => .Scase e n
  | .Default => .Sdefault

def make_slabeled : SwitchLabel × Location × C.Stmt → C.Stmt
  | (l, loc, s) => .mk (.Slabeled (label_of_switchlabel l) s) loc

def make_sequence (sl : List C.Stmt) : C.Stmt := sl.foldr (sseq no_loc) sskip

def make_normalized_switch (e : Exp) (cases : List (SwitchLabel × Location × C.Stmt)) :
    StmtDesc :=
  .Sswitch e (make_sequence (cases.map make_slabeled))

partial def all_cases (accu : List SwitchLabel) (s : C.Stmt) : M (List SwitchLabel) := do
  match s.sdesc with
  | .Sseq s1 s2 => all_cases (← all_cases accu s1) s2
  | .Sif _ s1 s2 => all_cases (← all_cases accu s1) s2
  | .Swhile _ s1 => all_cases accu s1
  | .Sdowhile s1 _ => all_cases accu s1
  | .Sfor s1 _ s2 s3 => all_cases (← all_cases (← all_cases accu s1) s2) s3
  | .Sswitch _ _ => return accu
  | .Slabeled (.Scase e n) s1 => all_cases (.Case e n :: accu) s1
  | .Slabeled .Sdefault s1 => all_cases (.Default :: accu) s1
  | .Slabeled (.Slabel _) s1 => all_cases accu s1
  | .Sblock _ => assertFalse "SwitchNorm.all_cases"
  | _ => return accu

partial def substitute_cases (case_table : List (SwitchLabel × String)) (body : C.Stmt)
    (end_label : String) : M C.Stmt :=
  transf false body
where
  transf_label : SLabel → M SLabel
    | .Scase e n => match case_table.lookup (.Case e n) with
        | some l => pure (.Slabel l)
        | none => assertFalse "SwitchNorm.substitute_cases"
    | .Sdefault => match case_table.lookup .Default with
        | some l => pure (.Slabel l)
        | none => assertFalse "SwitchNorm.substitute_cases"
    | lbl@(.Slabel _) => pure lbl
  transf (inloop : Bool) (s : C.Stmt) : M C.Stmt := do
    let d ← match s.sdesc with
      | .Sseq s1 s2 => pure (StmtDesc.Sseq (← transf inloop s1) (← transf inloop s2))
      | .Sif e s1 s2 => pure (.Sif e (← transf inloop s1) (← transf inloop s2))
      | .Swhile e s1 => pure (.Swhile e (← transf true s1))
      | .Sdowhile s1 e => pure (.Sdowhile (← transf true s1) e)
      | .Sfor s1 e s2 s3 =>
          pure (.Sfor (← transf inloop s1) e (← transf inloop s2) (← transf true s3))
      | .Sbreak => pure (if inloop then .Sbreak else .Sgoto end_label)
      | .Slabeled lbl s1 => pure (.Slabeled (← transf_label lbl) (← transf inloop s1))
      | .Sblock _ => assertFalse "SwitchNorm.substitute_cases"
      | sd => pure sd
    return .mk d s.sloc

partial def is_skip_or_debug (s : C.Stmt) : Bool :=
  match s.sdesc with
  | .Sseq a b => is_skip_or_debug a && is_skip_or_debug b
  | .Sskip => true
  | _ => is_debug_stmt s

/-- The state of the transformation: `support_unstructured` and the label
    counter `new_label`. -/
abbrev SM := StateT (Bool × Nat) M

def gen_label : SM String := do
  modify fun (u, n) => (u, n + 1)
  return s!"@{(← get).2}"

def normalize_switch (loc : Location) (e : Exp) (body : C.Stmt) : SM StmtDesc := do
  let (init, cases) := group_switch (flatten_switch [body])
  let allcases := (← all_cases [] body).reverse
  if is_skip_or_debug init && cases.length == allcases.length then
    -- This is a structured switch
    return make_normalized_switch e cases
  else
    -- This switch needs to be converted
    if !(← get).1 then
      Diagnostics.error loc
        ("unsupported feature: non-structured 'switch' statement " ++
         "(consider adding option [-funstructured-switch])")
    let case_table ← allcases.mapM fun case => do return (case, ← gen_label)
    let end_lbl ← gen_label
    let newbody ← substitute_cases case_table body end_lbl
    let goto_case : SwitchLabel × String → SwitchLabel × Location × C.Stmt :=
      fun (case, lbl) => (case, no_loc, .mk (.Sgoto lbl) no_loc)
    let case_table' :=
      if case_table.any (·.1 == .Default) then case_table
      else (.Default, end_lbl) :: case_table
    return .Sseq (.mk (make_normalized_switch e (case_table'.map goto_case)) loc)
      (sseq no_loc newbody (.mk (.Slabeled (.Slabel end_lbl) sskip) no_loc))

partial def transform_stmt (s : C.Stmt) : SM C.Stmt := do
  let d ← match s.sdesc with
    | .Sseq s1 s2 => pure (StmtDesc.Sseq (← transform_stmt s1) (← transform_stmt s2))
    | .Sif e s1 s2 => pure (.Sif e (← transform_stmt s1) (← transform_stmt s2))
    | .Swhile e s1 => pure (.Swhile e (← transform_stmt s1))
    | .Sdowhile s1 e => pure (.Sdowhile (← transform_stmt s1) e)
    | .Sfor s1 e s2 s3 =>
        pure (.Sfor (← transform_stmt s1) e (← transform_stmt s2) (← transform_stmt s3))
    | .Sswitch e s1 => normalize_switch s.sloc e (← transform_stmt s1)
    | .Slabeled lbl s1 => pure (.Slabeled lbl (← transform_stmt s1))
    | .Sblock sl => pure (.Sblock (← sl.mapM transform_stmt))
    | sd => pure sd
  return .mk d s.sloc

/-- Entry point (`Transform.program ~fundef:transform_fundef`; the other
    hooks of `Transform.program` are the identity and the environment it
    threads is not used by `transform_fundef`, so the declarations are
    traversed directly).  The label counter is threaded through the
    functions of the program. -/
def program (unstructured : Bool) (p : Program) : M Program := do
  let mut n : Nat := 0
  let mut out : Array Globdecl := #[]
  for g in p do
    match g.gdesc with
    | .Gfundef fd =>
        let (body, (_, n')) ← (transform_stmt fd.fd_body).run (unstructured, n)
        n := n'
        out := out.push { g with gdesc := .Gfundef { fd with fd_body := body } }
    | _ => out := out.push g
  return out.toList

end SwitchNorm
end CParser
end CC
