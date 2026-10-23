/-
  aiT annotations (`__builtin_ais_annot`) — port of `backend/AisAnnot.ml`.

  An annotation of kind 2 is a text with parameters `%eN` (expression),
  `%lN` (l-value), `%here` (the address of the annotation) and `%%`.  The
  assembly printers record the annotation, with its parameters replaced by
  aiT expressions over registers and memory, and `PrintAsm` emits the
  recorded annotations in the section `__compcert_ais_annotations`; the
  `AsmToJSON` back ends export them as JSON.

  Differences from OCaml:
  * The global list `ais_annot_list` is the field `aisAnnots` of the printer
    state (`PrintAsmaux.State`); `add_ais_annot` is
    `PrintAsmaux.addAisAnnot`, `get_ais_annots` is
    `PrintAsmaux.getAisAnnots`.
  * `Str.full_split` with the regular expression
    `%%\|%[el][0-9]+\|%here\|\007` is the hand-written `split`.
  * The warning `Wrong_ais_parameter` is returned (as `Warning`) instead of
    being printed; the `assert false` of OCaml (float arguments) and the
    failure of `List.nth` (a parameter number with no argument) are errors
    of the `Except String` result.
  * `validate_ais_annot` (the check made by `C2C` on the C arguments of
    `__builtin_ais_annot`) runs in the front-end monad `CParser.M`, which
    holds the diagnostics; OCaml's `with _ ->` catches every exception of
    the front end (`Exn`).  `C2C` calls it on `__builtin_ais_annot`.
-/
import CCLib.common.Memdata
import CCLib.lib.Camlcoq
import CCLib.cparser.Cutil

namespace CC
namespace AisAnnot

/-- `AisAnnot.t`: a piece of an annotation. -/
inductive T where
  | Label (lbl : Nat)
  | String (s : _root_.String)
  | Symbol (id : Ident)
  deriving Inhabited, BEq, Repr

/-- `AisAnnot.offset` -/
def offset (ofs : Integers.Ptrofs) : _root_.String :=
  let o := Integers.Int.signed (Integers.Int.repr (Integers.Ptrofs.unsigned ofs))
  if o = 0 then "" else s!" + {o}"

/-- `AisAnnot.size_chunk` -/
def sizeChunkStr (c : Chunk) : _root_.String := toString (sizeChunk c)

/-- `AisAnnot.addr_global` -/
def addrGlobal (id : Ident) (ofs : Integers.Ptrofs) : List T :=
  [.String "(", .Symbol id, .String s!"{offset ofs})"]

/-- `AisAnnot.warn_lval_arg`: `some msg` is the exception
    `Bad_parameter msg`. -/
def warnLvalArg {A : Type} (pos : _root_.String) : BuiltinArg A → Except _root_.String (Option _root_.String)
  | .BA_int _ | .BA_long _ | .BA_addrstack _ | .BA_addrglobal _ _ | .BA_splitlong _ _
  | .BA_addptr _ _ =>
    .ok (some s!"expected register or memory cell for parameter '{pos}', skipping generation of ais annotation")
  | .BA_float _ | .BA_single _ => .error "AisAnnot.warn_lval_arg: float argument"
  | _ => .ok none

/-- `AisAnnot.ais_expr_arg` -/
def aisExprArg {A : Type} (pregString : A → _root_.String) (spRegName : _root_.String) :
    BuiltinArg A → Except _root_.String (List T)
  | .BA x => .ok [.String s!"reg(\"{pregString x}\")"]
  | .BA_int n => .ok [.String (toString (Integers.Int.signed n))]
  | .BA_long n => .ok [.String (toString (Integers.Int64.signed n))]
  | .BA_float _ | .BA_single _ => .error "AisAnnot.ais_expr_arg: float argument"
  | .BA_loadstack chunk ofs =>
    .ok [.String s!"mem(reg(\"{spRegName}\"){offset ofs}, {sizeChunkStr chunk})"]
  | .BA_addrstack ofs => .ok [.String s!"(reg(\"{spRegName}\"){offset ofs})"]
  | .BA_loadglobal chunk id ofs =>
    .ok [.String "mem(", .Symbol id, .String s!"{offset ofs}, {sizeChunkStr chunk})"]
  | .BA_addrglobal id ofs => .ok (addrGlobal id ofs)
  | .BA_splitlong hi lo => do
    let arg1 := combine " * " (← aisExprArg pregString spRegName hi) [.String "0x100000000"]
    return combine " + " arg1 (← aisExprArg pregString spRegName lo)
  | .BA_addptr a1 a2 => do
    return combine " + " (← aisExprArg pregString spRegName a1) (← aisExprArg pregString spRegName a2)
where
  combine (mid : _root_.String) (arg1 arg2 : List T) : List T :=
    [.String "("] ++ arg1 ++ [.String mid] ++ arg2 ++ [.String ")"]

/-- A token of `Str.full_split`. -/
inductive Tok where
  | Text (s : _root_.String)
  | Delim (s : _root_.String)
  deriving BEq, Repr

/-- `Str.full_split re_ais_annot_param txt`, with `re_ais_annot_param` =
    `%%\|%[el][0-9]+\|%here\|\007`. -/
def split (txt : _root_.String) : List Tok :=
  go txt.toList [] txt.length
where
  flush (acc : List Char) : List Tok :=
    if acc.isEmpty then [] else [.Text (_root_.String.ofList acc.reverse)]
  go (cs : List Char) (acc : List Char) : Nat → List Tok
    | 0 => flush acc
    | fuel + 1 =>
      match cs with
      | [] => flush acc
      | '%' :: '%' :: rest => flush acc ++ .Delim "%%" :: go rest [] fuel
      | '%' :: 'h' :: 'e' :: 'r' :: 'e' :: rest => flush acc ++ .Delim "%here" :: go rest [] fuel
      | '%' :: c :: rest =>
        let ds := rest.takeWhile Char.isDigit
        if (c == 'e' || c == 'l') && !ds.isEmpty then
          flush acc ++ .Delim (_root_.String.ofList ('%' :: c :: ds)) :: go (rest.drop ds.length) [] fuel
        else go (c :: rest) ('%' :: acc) fuel
      | '\x07' :: rest => flush acc ++ .Delim "\x07" :: go rest [] fuel
      | c :: rest => go rest (c :: acc) fuel

#guard split "a %e1 b%%c%here\x07%x" ==
  [.Text "a ", .Delim "%e1", .Text " b", .Delim "%%", .Text "c", .Delim "%here", .Delim "\x07",
   .Text "%x"]

/-- `AisAnnot.loc_of_txt`: the location `# file:F line:L` at the start of
    the first line (without its last character, as in OCaml). -/
def locOfTxt (txt : _root_.String) : Option (_root_.String × Nat) := do
  let cs := txt.toList
  let pos ← cs.findIdx? (· == '\n')
  let line := cs.take (pos - 1)
  let rest ← (_root_.String.ofList line).dropPrefix? "# file:"
  let rest := rest.toString.toList
  let file := rest.takeWhile (· != ' ')
  if file.isEmpty then none
  let rest := rest.drop file.length
  let rest ← (_root_.String.ofList rest).dropPrefix? " line:"
  let l := rest.toString.toList.takeWhile (· != ' ')
  let n ← (_root_.String.ofList l).toNat?
  return (_root_.String.ofList file, n)

/-- The warning `Wrong_ais_parameter`: its location (if the text starts with
    one) and its message. -/
structure Warning where
  loc : Option (_root_.String × Nat)
  msg : _root_.String
  deriving Repr

/-- `AisAnnot.ais_annot_txt`: the annotation, and the warning if a
    parameter is not acceptable (the annotation is then empty). -/
def aisAnnotTxt {A : Type} (warn : Bool) (lbl : Nat) (pregString : A → _root_.String)
    (spRegName : _root_.String) (txt : _root_.String) (args : List (BuiltinArg A)) :
    Except _root_.String (List T × Option Warning) := do
  let fragment : Tok → Except _root_.String (Except _root_.String (List T)) := fun
    | .Delim "%here" => pure (.ok [.Label lbl])
    | .Text s => pure (.ok [.String s])
    | .Delim "%%" => pure (.ok [.String "%"])
    | .Delim "\x07" => pure (.ok [.String "\x07\x00"])
    | .Delim s => do
      let cs := s.toList
      let typ := cs.getD 1 ' '
      let n := (_root_.String.ofList (cs.drop 2)).toNat!
      let some arg := args[n - 1]? | throw s!"AisAnnot: no argument for parameter {s}"
      match typ with
      | 'e' => return .ok (← aisExprArg pregString spRegName arg)
      | 'l' =>
        match ← warnLvalArg s arg with
        | some msg => return .error msg
        | none => return .ok (← aisExprArg pregString spRegName arg)
      | _ => throw "AisAnnot.ais_annot_txt"
  -- `List.concat (List.map fragment ...)`, stopping at the first `Bad_parameter`
  let rec frags : List Tok → Except _root_.String (Except _root_.String (List T))
    | [] => pure (.ok [])
    | t :: ts => do
      match ← fragment t with
      | .error m => return .error m
      | .ok l =>
        match ← frags ts with
        | .error m => return .error m
        | .ok l' => return .ok (l ++ l')
  let (annot, warning) : List T × Option Warning := match ← frags (split txt) with
    | .ok l => (l, none)
    | .error m => ([], if warn then some { loc := locOfTxt txt, msg := s!"wrong ais parameter: {m}" } else none)
  let rec merge (acc : List T) : List T → List T
    | [] => acc
    | .Label l :: rest => merge (.Label l :: acc) rest
    | .Symbol s :: rest => merge (.Symbol s :: acc) rest
    | .String s1 :: .String s2 :: rest => merge acc (.String (s1 ++ s2) :: rest)
    | .String s :: rest => merge (.String s :: acc) rest
  termination_by l => (l.length, match l with | .String _ :: .String _ :: _ => 0 | _ => 1)
  decreasing_by all_goals simp_wf <;> omega
  let revAnnot : List T := match merge [] annot with
    | [] => []
    | .String s :: rest => .String (s ++ "\n") :: rest
    | rest => .String "\n" :: rest
  return (revAnnot.reverse, warning)

/-- `AisAnnot.json_ais_annot`: the annotation for the JSON output
    (`%here` stays as is; backslashes and double quotes are escaped). -/
def jsonAisAnnot {A : Type} (pregString : A → _root_.String) (spRegName : _root_.String)
    (txt : _root_.String) (args : List (BuiltinArg A)) : Except _root_.String (List T) := do
  let (txt, _) ← aisAnnotTxt false 0 pregString spRegName txt args
  return txt.map fun
    | .Label _ => .String "%here"
    | .String s =>
      .String (_root_.String.join (s.toList.map fun c =>
        if c == '\\' || c == '"' then "\\" ++ c.toString else c.toString))
    | .Symbol s => .Symbol s

#guard (aisAnnotTxt (A := Nat) true 7 toString "sp" "x=%e1 at %here" [.BA 3]).toOption.map (·.1)
  == some [.String "x=reg(\"3\") at ", .Label 7, .String "\n"]
#guard ((aisAnnotTxt (A := Nat) true 7 toString "sp" "%l1" [.BA_int 3]).toOption.map (·.1))
  == some []

/-- `validate_ais_annot env loc txt args`: check the C arguments of an
    annotation of kind 2 (no floating-point arguments, no volatile
    variables, no unknown parameter) and warn about unused parameters. -/
def validate_ais_annot (env : CParser.Env.T) (loc : CParser.C.Location) (txt : _root_.String)
    (args : List CParser.C.Exp) : CParser.M Unit := do
  let mut used_params : Array Bool := Array.replicate args.length false
  for arg in split txt do
    match arg with
    | .Delim "%here" | .Text _ | .Delim "%%" | .Delim "\x07" => pure ()
    | .Delim s =>
      let check : StateT (Array Bool) CParser.M Unit := do
        let n ← match ((s.drop 2).toString).toNat? with
          | some n => pure n
          | none => throw (.Failure "int_of_string")
        if n = 0 then throw (.Failure "List.nth")
        let arg ← match args[n - 1]? with
          | some a => pure a
          | none => throw (.Failure "nth")
        modify fun u => u.set! (n - 1) true
        if ← CParser.Cutil.is_float_type env arg.etyp then
          CParser.Diagnostics.error loc
            s!"floating point types for parameter '{s}' are not supported in ais annotations"
        else if ← CParser.Cutil.is_volatile_variable env arg then
          let arg ← match arg.edesc with
            | .EVar id => pure id.name
            | _ => CParser.assertFalse "AisAnnot.validate_ais_annot"
          CParser.Diagnostics.error loc
            s!"access to volatile variable '{arg}' for parameter '{s}' is not supported in ais annotations"
      -- as in OCaml, the updates of `used_params` done before an exception are kept
      let saved := used_params
      let r : CParser.M (Unit × Array Bool) := tryCatch (check.run saved) fun _ => do
        let u := match (((s.drop 2).toString).toNat?) with
          | some n => if n ≥ 1 && n ≤ args.length then saved.set! (n - 1) true else saved
          | none => saved
        CParser.Diagnostics.error loc s!"unknown parameter '{s}'"
        pure ((), u)
      let (_, u) ← r
      used_params := u
  for pos in [0:used_params.size] do
    if !used_params[pos]! then
      CParser.Diagnostics.warning loc .Unused_ais_parameter s!"unused parameter {pos} of ais annotation"

/-- The diagnostics of `validate_ais_annot` on a test. -/
def validateMessages (txt : _root_.String) (args : List CParser.C.Exp) : Array _root_.String :=
  match (validate_ais_annot CParser.Env.empty ("t.c", 1) txt args).run
      { config := CParser.Machine.x86_64 } with
  | .ok _ st => st.messages
  | .error _ st => st.messages

#guard (validateMessages "%e1"
  [.mk (.EVar ⟨"x", 1⟩) (.TInt .IInt [])]).size == 0
#guard (validateMessages "%e1 %e3"
  [.mk (.EVar ⟨"x", 1⟩) (.TInt .IInt []), .mk (.EVar ⟨"y", 2⟩) (.TInt .IInt [])]).size == 2
#guard (validateMessages "%e1"
  [.mk (.EVar ⟨"f", 1⟩) (.TFloat .FDouble [])]).size == 1

end AisAnnot
end CC
