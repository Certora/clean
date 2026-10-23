/-
  Interpreting CompCert C sources — port of `driver/Interp.ml`, the reference
  interpreter behind `ccomp -interp`.

  The interpreter animates the CompCert C semantics with the executable
  transition function `Cexec.doStep` (`CCLib.cfrontend.Cexec`, proved sound and
  complete for `Csem` in `CCLib.cfrontend.CexecStep`).  It explores one
  execution (`-interp`, `-random`) or all executions (`-all`), prints the
  observable events, emulates `printf`, and stops on undefined behaviour with
  exit code 126.

  Differences with the OCaml version:
  * The OCaml `do_external_function` prints the output of `printf` while it
    computes the transition.  `Cexec.ExtOracle` is pure here, so the oracle
    (`doExternalFunction`) only computes the result and the event, and
    `doStepIO` prints the formatted text of every `printf` event of the
    computed transitions (from the event's arguments and the memory of the
    state), at the same point of the execution.
  * `printf` is emulated by `doPrintf` (a hand-written parser of the ISO C 99
    conversions instead of `Str` regular expressions; the conversions are
    computed exactly from the bit patterns, as the other printers of the port).
  * States are printed with `PrintCsyntax`, whose pointer hook prints nothing
    (pointers print as `<ptr>`, locations as `<loc>`).
  * In `-all` mode the OCaml interpreter merges identical states with a map
    ordered by `compare_state`.  States contain reduction contexts (functions)
    and types without a derived equality, so here each state is encoded as a
    string key (`stateKey`) built from the components that `compare_state`
    compares (memory contents and next block, functions, statements,
    environments, continuations, reduction contexts applied to `some_expr`),
    and states with equal keys are merged (`Std.HashMap`).  The keys are
    written with dedicated printers (`valKey`, `memvalKey`, `tyKey`, …), not
    `reprStr`, whose `Format` rendering dominated the running time.  As in the
    OCaml version, memories are compared with the contents of freed blocks, so
    calls evaluated in different orders give different states even when the
    results agree: a loop with two such calls per iteration doubles the
    number of states at every iteration (see the `-all` examples of
    `examples/InterpSpec.lean`, run by `lake test`).
  * `explore_one` and `explore_all` stop (exit code 124) when the task
    running them is cancelled, so that a test harness can stop a run that
    exceeds its time limit.
  * `World` is in `Type 1` (`CCLib.common.Worlds`) and cannot be the result
    of an `IO` action: the interpreter carries the memory of the world
    (`world wge wm`) instead of the world itself.
  * The OCaml `exit` becomes `Stop.Exit` (the driver turns it into the exit
    code of the process).
-/
import CCLib.cfrontend.Cexec
import CCLib.cfrontend.PrintCsyntax
import CCLib.driver.Driveraux
import Std.Data.HashMap

namespace CC
namespace Interp

open Csyntax Csem Cexec Camlcoq Format Driveraux

/-! ## Printing events -/

/-- `print_id_ofs` -/
def printIdOfs (id : Ident) (ofs : Integers.Ptrofs) : String :=
  let o := wrapSigned 32 (Integers.Ptrofs.unsigned ofs)
  if o == 0 then s!" {externAtom id}"
  else s!" {externAtom id}{if o > 0 then "+" else ""}{o}"

/-- `print_eventval` -/
def printEventval : EventVal → String
  | .EVint n => ci32 n
  | .EVfloat f => floatF f 15
  | .EVsingle f => float32F f 15
  | .EVlong n => ci64 n ++ "LL"
  | .EVptr_global id ofs => "&" ++ printIdOfs id ofs

/-- `print_eventval_list` -/
def printEventvalList (vl : List EventVal) : String :=
  ", ".intercalate (vl.map printEventval)

/-- `%+ld` -/
def signedOfs (ofs : Integers.Ptrofs) : String :=
  let o := wrapSigned 32 (Integers.Ptrofs.unsigned ofs)
  (if o ≥ 0 then "+" else "") ++ toString o

/-- `print_event` -/
def printEvent : Event → String
  | .Event_syscall id args res =>
    s!"extcall {id}({printEventvalList args}) -> {printEventval res}"
  | .Event_vload chunk id ofs res =>
    s!"volatile load {PrintAST.nameOfChunk chunk}[&{externAtom id}{signedOfs ofs}] -> {printEventval res}"
  | .Event_vstore chunk id ofs arg =>
    s!"volatile store {PrintAST.nameOfChunk chunk}[&{externAtom id}{signedOfs ofs}] <- {printEventval arg}"
  | .Event_annot text args =>
    s!"annotation \"{text}\" {printEventvalList args}"

#guard printEvent (.Event_syscall "printf" [.EVint (Integers.Int.repr 3)] (.EVint (Integers.Int.repr 4)))
  = "extcall printf(3) -> 4"

/-! ## Printing states -/

/-- `name_of_fundef`.  OCaml compares function definitions physically (`==`);
    here a definition is found by the name of the function being called, or
    by structural equality of the internal function's body. -/
def nameOfFundef (prog : Csyntax.Program) (fd : Csyntax.FunDef) : String :=
  let sameFd : Csyntax.FunDef → Bool := fun fd' =>
    match fd, fd' with
    | .Internal f, .Internal f' =>
      render (PrintCsyntax.printStmt f.fn_body) == render (PrintCsyntax.printStmt f'.fn_body) &&
        PrintCsyntax.nameType f.fn_return == PrintCsyntax.nameType f'.fn_return
    | .External ef1 _ _ _, .External ef2 _ _ _ =>
      PrintAST.nameOfExternal ef1 == PrintAST.nameOfExternal ef2
    | _, _ => false
  match prog.prog_defs.find? (fun (_, gd) => match gd with
      | .Gfun fd' => sameFd fd' | .Gvar _ => false) with
  | some (id, _) => externAtom id
  | none => "<unknown function>"

/-- `name_of_function` -/
def nameOfFunction (prog : Csyntax.Program) (fn : Csyntax.Function) : String :=
  nameOfFundef prog (.Internal fn)

/-- `print_val_list` -/
def printValList (vl : List Val) : Doc :=
  match vl with
  | [] => #[]
  | v1 :: vl => vl.foldl (fun d v => d ++ ppf ",@ " ++ txt (PrintCsyntax.printValue v))
      (txt (PrintCsyntax.printValue v1))

/-- `print_state` -/
def printState (prog : Csyntax.Program) : Csem.State → Doc
  | .State f s _ _ _ =>
    txt s!"in function {nameOfFunction prog f}, statement" ++ ppf "@ @[<hv 0>" ++
      PrintCsyntax.printStmt s ++ ppf "@]"
  | .ExprState f r _ _ _ =>
    txt s!"in function {nameOfFunction prog f}, expression" ++ ppf "@ @[<hv 0>" ++
      PrintCsyntax.printExpr r ++ ppf "@]"
  | .Callstate fd args _ _ =>
    ppf "calling@ @[<hov 2>" ++ txt (nameOfFundef prog fd) ++ txt "(" ++ printValList args ++
      txt ")" ++ ppf "@]"
  | .Returnstate res _ _ => ppf "returning@ " ++ txt (PrintCsyntax.printValue res)
  | .Stuckstate => txt "stuck after an undefined expression"

/-- Print a document in a `hov 2` box, followed by a newline. -/
def printLine (d : Doc) : IO Unit := do
  IO.println (render (ppf "@[<hov 2>" ++ d ++ ppf "@]") 78 30)
  (← IO.getStdout).flush

/-! ## Extracting a string from memory -/

/-- `extract_string m blk ofs` (with fuel: a string has at most `fuel` bytes). -/
def extractString (m : Mem) (blk : Block) (ofs : Z) : Option String :=
  go 1000000 ofs #[]
where
  go : Nat → Z → Array UInt8 → Option String
    | 0, _, _ => none
    | fuel + 1, ofs, acc =>
      match Mem.load .Mint8unsigned m blk ofs with
      | some (.Vint n) =>
        let c := (Integers.Int.unsigned n).toNat
        if c == 0 then some (String.fromUTF8? (ByteArray.mk acc) |>.getD
            (String.ofList (acc.toList.map fun b => Char.ofNat b.toNat)))
        else go fuel (ofs + 1) (acc.push c.toUInt8)
      | _ => none

/-! ## Emulation of `printf` -/

/-- A parsed conversion specification `%<flags><width>.<prec><length><conv>`. -/
structure Spec where
  flags : List Char
  width : Nat
  prec : Option Nat
  length : String
  conv : Char

/-- Parse a conversion specification after a `%` (the regular expression
    `re_conversion`); returns the specification and the position after it. -/
def parseSpec (s : Array Char) (pos : Nat) : Option (Spec × Nat) := Id.run do
  let mut i := pos
  let mut flags : List Char := []
  while i < s.size && "-+0# ".toList.contains s[i]! do
    flags := flags ++ [s[i]!]; i := i + 1
  let mut width := 0
  while i < s.size && s[i]!.isDigit do
    width := width * 10 + (s[i]!.toNat - '0'.toNat); i := i + 1
  let mut prec : Option Nat := none
  if i < s.size && s[i]! == '.' then
    i := i + 1
    let mut p := 0
    while i < s.size && s[i]!.isDigit do
      p := p * 10 + (s[i]!.toNat - '0'.toNat); i := i + 1
    prec := some p
  let mut length := ""
  if i + 1 < s.size && ((s[i]! == 'h' && s[i+1]! == 'h') || (s[i]! == 'l' && s[i+1]! == 'l')) then
    length := String.ofList [s[i]!, s[i+1]!]; i := i + 2
  else if i < s.size && "lhjztL".toList.contains s[i]! then
    length := String.singleton s[i]!; i := i + 1
  if i < s.size && "aAcdeEfgGinopsuxX%".toList.contains s[i]! then
    return some ({ flags, width, prec, length, conv := s[i]! }, i + 1)
  return none

/-- Pad `body` (preceded by `prefix`: sign or `0x`) to the field width. -/
def pad (sp : Spec) (pre body : String) (zeroOk : Bool := true) : String :=
  let len := pre.length + body.length
  if len ≥ sp.width then pre ++ body
  else
    let n := sp.width - len
    if sp.flags.contains '-' then pre ++ body ++ String.ofList (List.replicate n ' ')
    else if sp.flags.contains '0' && zeroOk then
      pre ++ String.ofList (List.replicate n '0') ++ body
    else String.ofList (List.replicate n ' ') ++ pre ++ body

/-- C's integer conversions `d i u o x X` on an integer of `w` bits. -/
def formatInt (sp : Spec) (w : Nat) (z : Int) : String :=
  let signed := sp.conv == 'd' || sp.conv == 'i'
  let v : Int := if signed then wrapSigned w z else z % (2 ^ w : Nat)
  let mag := v.natAbs
  let digits : String :=
    match sp.conv with
    | 'o' => String.ofList (Nat.toDigits 8 mag)
    | 'x' => String.ofList (Nat.toDigits 16 mag)
    | 'X' => (String.ofList (Nat.toDigits 16 mag)).toUpper
    | _ => toString mag
  let digits := match sp.prec with
    | some 0 => if mag == 0 then "" else digits
    | some p => padZeros p digits
    | none => digits
  let pre :=
    if signed then (if v < 0 then "-" else if sp.flags.contains '+' then "+"
      else if sp.flags.contains ' ' then " " else "")
    else if sp.flags.contains '#' && mag != 0 then
      (match sp.conv with | 'x' => "0x" | 'X' => "0X" | _ => "")
    else ""
  let digits := if sp.conv == 'o' && sp.flags.contains '#' && !digits.startsWith "0" then
    "0" ++ digits else digits
  pad sp pre digits (zeroOk := sp.prec.isNone)

/-- `%.<p>f` of a finite non-negative rational `n/d`. -/
def fixedPos (p : Nat) (n d : Nat) : String :=
  let q := scaleRound n d p
  let s := padZeros (p + 1) (toString q)
  let ip := (s.take (s.length - p)).toString
  let fp := (s.drop (s.length - p)).toString
  if p == 0 then ip else ip ++ "." ++ fp

/-- `%.<p>e` of a finite non-negative rational `n/d`. -/
def expPos (p : Nat) (n d : Nat) (upper : Bool) : String :=
  let (x, sc) : Int × Nat :=
    if n == 0 then (0, 0) else
    let x0 := floorLog10 n d
    let sc0 := scaleRound n d ((p : Int) - x0)
    if sc0 ≥ 10 ^ (p + 1) then (x0 + 1, sc0 / 10) else (x0, sc0)
  let digits := padZeros (p + 1) (toString sc)
  let mant := (digits.take 1).toString ++ (if p == 0 then "" else "." ++ (digits.drop 1).toString)
  let ex := (if x < 0 then "-" else "+") ++ padZeros 2 (toString x.natAbs)
  mant ++ (if upper then "E" else "e") ++ ex

/-- C's floating-point conversions `f e E g G a` (`a` is printed as `g`). -/
def formatFloat (sp : Spec) (v : IEEEValue) : String :=
  let p := sp.prec.getD 6
  let signOf (neg : Bool) := if neg then "-" else if sp.flags.contains '+' then "+"
    else if sp.flags.contains ' ' then " " else ""
  match v with
  | .nan => pad sp "" "nan" false
  | .inf neg => pad sp (signOf neg) "inf" false
  | .finite neg n d =>
    let body := match sp.conv with
      | 'f' => fixedPos p n d
      | 'e' => expPos p n d false
      | 'E' => expPos p n d true
      | 'G' => (formatGPos p n d).toUpper
      | _ => formatGPos p n d
    pad sp (signOf (neg && n != 0)) body

/-- `format_value m flags length conv arg` -/
def formatValue (m : Mem) (sp : Spec) (arg : Val) : String :=
  let intConv := "diuoxXc".toList.contains sp.conv
  let shortLen := ["", "h", "hh", "l", "z", "t"].contains sp.length
  let longLen := ["ll", "j"].contains sp.length
  if intConv && shortLen then
    match arg with
    | .Vint i =>
      if sp.conv == 'c' then
        pad sp "" (String.singleton (Char.ofNat ((Integers.Int.unsigned i).toNat % 256))) false
      else formatInt sp 32 (Integers.Int.unsigned i)
    | _ => "<int argument expected>"
  else if sp.conv != 'c' && intConv && longLen then
    match arg with
    | .Vlong i => formatInt sp 64 (Integers.Int64.unsigned i)
    | _ => "<long long argument expected"
  else if "feEgGa".toList.contains sp.conv && (sp.length == "" || sp.length == "l") then
    match arg with
    | .Vfloat f => formatFloat sp (decodeIEEE 11 52 (Integers.Int64.unsigned f.toBits).toNat)
    | _ => if sp.length == "" then "<float argument expected" else "<unrecognized format>"
  else if sp.conv == 's' && sp.length == "" then
    match arg with
    | .Vptr blk ofs =>
      match extractString m blk (Integers.Ptrofs.unsigned ofs) with
      | some s =>
        let s := match sp.prec with | some p => (s.take p).toString | none => s
        pad sp "" s false
      | none => "<bad string>"
    | _ => "<pointer argument expected>"
  else if sp.conv == 'p' && sp.length == "" then
    match arg with
    | .Vptr blk ofs => s!"<{blk.toNat}{signedOfs ofs}>"
    | .Vint i => formatInt { sp with conv := 'x' } 32 (Integers.Int.unsigned i)
    | _ => "<int or pointer argument expected>"
  else "<unrecognized format>"

/-- `do_printf m fmt args` -/
def doPrintf (m : Mem) (fmt : String) (args : List Val) : String := Id.run do
  let s := fmt.toList.toArray
  let mut out := ""
  let mut pos := 0
  let mut args := args
  let mut fuel := s.size + 1
  while pos < s.size && fuel > 0 do
    fuel := fuel - 1
    let c := s[pos]!
    if c == '%' then
      match parseSpec s (pos + 1) with
      | some (sp, pos') =>
        pos := pos'
        if sp.conv == '%' then out := out.push '%'
        else
          match args with
          | [] => out := out ++ "<missing argument>"
          | a :: rest =>
            out := out ++ formatValue m sp a
            args := rest
      | none => out := out.push c; pos := pos + 1
    else
      out := out.push c; pos := pos + 1
  return out

#guard doPrintf Mem.empty "x=%d, %5d|%-4x|%04u%%\n"
  [.Vint (Integers.Int.repr (-3)), .Vint (Integers.Int.repr 42), .Vint (Integers.Int.repr 255),
   .Vint (Integers.Int.repr 7)] = "x=-3,    42|ff  |0007%\n"
#guard doPrintf Mem.empty "%lld %llx" [.Vlong (Integers.Int64.repr (-5)),
  .Vlong (Integers.Int64.repr 4096)] = "-5 1000"
#guard doPrintf Mem.empty "%d %d" [.Vint (Integers.Int.repr 1)] = "1 <missing argument>"
#guard formatFloat { flags := [], width := 0, prec := none, length := "", conv := 'f' }
  (.finite false 5 2) = "2.500000"
#guard formatFloat { flags := [], width := 0, prec := some 2, length := "", conv := 'e' }
  (.finite true 12345 1) = "-1.23e+04"
#guard formatFloat { flags := [], width := 0, prec := none, length := "", conv := 'g' }
  (.finite false 1 3) = "0.333333"

/-! ## External functions -/

/-- `convert_external_arg`: like `eventval_of_val`, but accepts static
    globals as well. -/
def convertExternalArg (ge : Senv) (v : Val) : Option EventVal :=
  match v with
  | .Vint i => some (.EVint i)
  | .Vfloat f => some (.EVfloat f)
  | .Vsingle f => some (.EVsingle f)
  | .Vlong n => some (.EVlong n)
  | .Vptr b ofs => (ge.invert_symbol b).map fun id => .EVptr_global id ofs
  | .Vundef => none

/-- `convert_external_args` -/
def convertExternalArgs {T : Type} (ge : Senv) : List Val → List T → Option (List EventVal)
  | [], [] => some []
  | v1 :: vl, _ :: tl => do
    let e1 ← convertExternalArg ge v1
    let el ← convertExternalArgs ge vl tl
    return e1 :: el
  | _, _ => none

/-- The output of a call to `printf` with arguments `args` in memory `m`. -/
def printfOutput (m : Mem) (args : List Val) : Option String :=
  match args with
  | .Vptr b ofs :: args' =>
    (extractString m b (Integers.Ptrofs.unsigned ofs)).map fun fmt => doPrintf m fmt args'
  | _ => none

/-- `do_external_function`, without the printing (see `doStepIO`). -/
def doExternalFunction : ExtDo := fun id sg ge w args m =>
  match id with
  | "printf" =>
    match printfOutput m args with
    | none => none
    | some fmt' =>
      let len := Integers.Int.repr (String.utf8ByteSize fmt')
      match convertExternalArgs ge args sg.sig_args with
      | none => none
      | some eargs => some (w, [.Event_syscall id eargs (.EVint len)], .Vint len, m)
  | _ => none

/-- The oracle of the interpreter (`do_inline_assembly` does nothing). -/
def oracle : ExtOracle :=
  { doExternalFunction := doExternalFunction
    doInlineAssembly := fun _ _ _ _ _ _ => none }

/-! ## The world: volatile variables -/

/-- `world ge m`: volatile loads and stores read and write the volatile
    variables of the world program, in memory `m`; system calls fail. -/
def world (ge : Csem.CGenv) (m : Mem) : World where
  σ := Mem
  st := m
  io := fun _ _ _ => none
  vload := fun m chunk id ofs => do
    let b ← Genv.findSymbol ge.genv_genv id
    let v ← Mem.load chunk m b (Integers.Ptrofs.unsigned ofs)
    let ev ← eventvalOfVal ge v chunk.typ
    return (ev, m)
  vstore := fun m chunk id ofs ev => do
    let b ← Genv.findSymbol ge.genv_genv id
    let v ← valOfEventval ge ev chunk.typ
    Mem.store chunk m b (Integers.Ptrofs.unsigned ofs) v

/-! ## The interpreter -/

/-- The verbosity (`trace`) and the mode. -/
structure Config where
  trace : Nat
  mode : InterpMode
  /-- the global environment of the world program (`world_program`) -/
  wge : Csem.CGenv

/-- `World` lives in `Type 1`, so it cannot be the result of an `IO` action.
    The worlds of the interpreter are all of the form `world cfg.wge wm`; the
    interpreter keeps the memory `wm` of the world and rebuilds the world
    from it. -/
def Config.world (cfg : Config) (wm : Mem) : World := Interp.world cfg.wge wm

/-- `do_event` -/
def doEvent (cfg : Config) (time : Nat) (w : Mem) (ev : Event) : IO Mem := do
  if cfg.trace ≥ 1 then
    printLine (txt s!"Time {time}: observable event:" ++ ppf "@ " ++ txt (printEvent ev))
  match ev with
  | .Event_vstore chunk id ofs v =>
    -- `nextworld_vstore (world wge w) chunk id ofs v = some (world wge w')`
    match (cfg.world w).vstore w chunk id ofs v with
    | some w' => return w'
    | none => return w
  | _ => return w

/-- `do_events` -/
def doEvents (cfg : Config) (time : Nat) (w : Mem) : Trace → IO Mem
  | [] => return w
  | ev :: t => do doEvents cfg time (← doEvent cfg time w ev) t

/-- `diagnose_stuck_expr`: print the innermost stuck subexpression. -/
partial def diagnoseStuckExpr (ge : Csem.CGenv) (w : World) (e : Env) (m : Mem) :
    Kind → Csyntax.Expr → IO Bool := fun k a => do
  let diag := diagnoseStuckExpr ge w e m
  let rec diagList : Csyntax.ExprList → IO Bool
    | .Enil => return false
    | .Econs a1 al => do
      let b1 ← diag .RV a1
      let b2 ← diagList al
      return b1 || b2
  let found ← match k, a with
    | .LV, .Ederef r _ => diag .RV r
    | .LV, .Efield r _ _ => diag .RV r
    | .RV, .Evalof l _ => diag .LV l
    | .RV, .Eaddrof l _ => diag .LV l
    | .RV, .Eunop _ r1 _ => diag .RV r1
    | .RV, .Ebinop _ r1 r2 _ => do let b1 ← diag .RV r1; let b2 ← diag .RV r2; pure (b1 || b2)
    | .RV, .Ecast r1 _ => diag .RV r1
    | .RV, .Econdition r1 _ _ _ => diag .RV r1
    | .RV, .Eassign l1 r2 _ => do let b1 ← diag .LV l1; let b2 ← diag .RV r2; pure (b1 || b2)
    | .RV, .Eassignop _ l1 r2 _ _ => do
      let b1 ← diag .LV l1; let b2 ← diag .RV r2; pure (b1 || b2)
    | .RV, .Epostincr _ l _ => diag .LV l
    | .RV, .Ecomma r1 _ _ => diag .RV r1
    | .RV, .Eparen r1 _ _ => diag .RV r1
    | .RV, .Ecall r1 rargs _ => do let b1 ← diag .RV r1; let b2 ← diagList rargs; pure (b1 || b2)
    | .RV, .Ebuiltin _ _ rargs _ => diagList rargs
    | _, _ => pure false
  if found then return true
  let l := stepExpr ge oracle e w k a m
  if l.any (fun (_, red) => match red with | .Stuckred => true | _ => false) then
    printLine (ppf "Stuck subexpression:@ " ++ PrintCsyntax.printExpr a)
    return true
  return false

/-- `diagnose_stuck_state` -/
def diagnoseStuckState (ge : Csem.CGenv) (w : World) : Csem.State → IO Unit
  | .ExprState _ a _ e m => do let _ ← diagnoseStuckExpr ge w e m .RV a
  | _ => pure ()

/-- The memory of a state. -/
def memOfState : Csem.State → Option Mem
  | .State _ _ _ _ m | .ExprState _ _ _ _ m | .Callstate _ _ _ m | .Returnstate _ _ m => some m
  | .Stuckstate => none

/-- The value of an event value (`EVptr_global id ofs` is the address of `id`). -/
def valOfEventvalAny (ge : Csem.CGenv) : EventVal → Option Val
  | .EVint i => some (.Vint i)
  | .EVlong i => some (.Vlong i)
  | .EVfloat f => some (.Vfloat f)
  | .EVsingle f => some (.Vsingle f)
  | .EVptr_global id ofs => (Genv.findSymbol ge.genv_genv id).map fun b => .Vptr b ofs

/-- `Cexec.do_step` with the oracle of the interpreter, printing the output
    of `printf` when a call to `printf` executes.  (In interpreter mode the
    front end turns calls to variadic external functions into builtins, so
    the call is found through the `printf` event of the transition; its
    arguments are those of the event, read in the memory of the state.) -/
def doStepIO (ge : Csem.CGenv) (w : World) (s : Csem.State) : IO (List Transition) := do
  let l := Cexec.doStep ge oracle w s
  if let some m := memOfState s then
    for .TR _ t _ in l do
      for ev in t do
        if let .Event_syscall "printf" eargs _ := ev then
          if let some args := eargs.mapM (valOfEventvalAny ge) then
            if let some out := printfOutput m args then
              IO.print out
              (← IO.getStdout).flush
  return l

/-- `do_step`: the successors of a state (rule, next state, next world).
    Throws `Stop.Exit` at the end of the program (modes `First`/`Random`)
    and on undefined behaviour. -/
def doStep (cfg : Config) (prog : Csyntax.Program) (ge : Csem.CGenv) (time : Nat)
    (s : Csem.State) (w : Mem) : DM (List (String × Csem.State × Mem)) := do
  match atFinalState s with
  | some r =>
    if cfg.trace ≥ 1 then
      io (printLine (txt s!"Time {time}: program terminated (exit code = {ci32 r})"))
    match cfg.mode with
    | .All => return []
    | .First | .Random => throwThe Stop (.Exit (wrapSigned 32 (Integers.Int.unsigned r)).toNat.toUInt32)
  | none =>
    let l ← io (doStepIO ge (cfg.world w) s)
    if l.isEmpty || l.any (fun (.TR _ _ s') => match s' with | .Stuckstate => true | _ => false)
    then
      io (printLine (ppf "Stuck state:@ " ++ printState prog s))
      io (diagnoseStuckState ge (cfg.world w) s)
      io (IO.println "ERROR: Undefined behavior")
      throwThe Stop (.Exit 126)
    else
      l.mapM fun (.TR r t s') => do return (r, s', ← io (doEvents cfg time w t))

/-- Stop (exit code 124) when the task running the interpreter was cancelled
    (not in the OCaml version: lets a test harness running the interpreter in
    a thread stop a run that exceeds its time limit). -/
def stopIfCanceled : DM Unit := do
  if ← io IO.checkCanceled then throwThe Stop (.Exit 124)

/-- `explore_one`: one execution (the first or a random successor at each
    step). -/
partial def exploreOne (cfg : Config) (prog : Csyntax.Program) (ge : Csem.CGenv)
    (time : Nat) (s : Csem.State) (w : Mem) : DM Unit := do
  stopIfCanceled
  if cfg.trace ≥ 2 then
    io (printLine (txt s!"Time {time}:" ++ ppf "@ " ++ printState prog s))
  let succs ← doStep cfg prog ge time s w
  match succs with
  | [] => return
  | first :: _ =>
    let (r, s', w') ← match cfg.mode with
      | .Random => do
        let i ← io (IO.rand 0 (succs.length - 1))
        pure (succs.getD i first)
      | _ => pure first
    if cfg.trace ≥ 2 then io (IO.println s!"--[{r}]-->")
    exploreOne cfg prog ge (time + 1) s' w'

/-! ## Identifying states (for `explore_all`)

The OCaml interpreter merges the states of a generation that are equal for
`compare_state` (memories are compared by their contents only, reduction
contexts by their value at a fixed expression `some_expr`).  Here a state is
mapped to a string key, an injective encoding of the same components, and
states with the same key are merged. -/

/-- A key for a value (`reprStr` goes through `Format` and is too slow for
    the keys of `explore_all`, computed at every transition). -/
def valKey : Val → String
  | .Vundef => "U"
  | .Vint n => s!"i{n.toNat}"
  | .Vlong n => s!"l{n.toNat}"
  | .Vfloat f => s!"f{f.bits.toNat}"
  | .Vsingle f => s!"s{f.bits.toNat}"
  | .Vptr b ofs => s!"p{b.toNat}+{ofs.toNat}"

/-- A key for a list of values. -/
def valsKey (vl : List Val) : String := "[" ++ ",".intercalate (vl.map valKey) ++ "]"

/-- A key for a memory value. -/
def memvalKey : MemVal → String
  | .Undef => "u"
  | .Byte b => toString b.toNat
  | .Fragment v q i => s!"F({valKey v},{match q with | .Q32 => 4 | .Q64 => 8},{i})"

/-- A key for type attributes. -/
def attrKey (a : Attr) : String :=
  (if a.attr_volatile then "v" else "") ++
    (match a.attr_alignas with | none => "" | some n => s!"@{n}")

/-- A key for a signedness. -/
def signKey : Signedness → String
  | .Signed => "s"
  | .Unsigned => "u"

/-- A key for an integer size. -/
def intSizeKey : IntSize → String
  | .I8 => "8" | .I16 => "16" | .I32 => "32" | .IBool => "b"

/-- A key for a calling convention. -/
def ccKey (cc : CallConv) : String :=
  s!"{match cc.cc_vararg with | none => "-" | some n => toString n}{cc.cc_unproto}{cc.cc_structret}"

/-- A key for a bit-field designator. -/
def bitfieldKey : Bitfield → String
  | .Full => "full"
  | .Bits sz sg pos width => s!"{intSizeKey sz}{signKey sg}:{pos}:{width}"

/-- A key for a type. -/
def tyKey : Ty → String
  | .Tvoid => "v"
  | .Tint sz sg a => s!"i({intSizeKey sz},{signKey sg},{attrKey a})"
  | .Tlong sg a => s!"l({signKey sg},{attrKey a})"
  | .Tfloat sz a => s!"f({match sz with | .F32 => 32 | .F64 => 64},{attrKey a})"
  | .Tpointer t a => s!"p({tyKey t},{attrKey a})"
  | .Tarray t sz a => s!"a({tyKey t},{sz},{attrKey a})"
  | .Tfunction targs tres cc => s!"F([{",".intercalate (targs.map tyKey)}],{tyKey tres},{ccKey cc})"
  | .Tstruct id a => s!"s({id.toNat},{attrKey a})"
  | .Tunion id a => s!"u({id.toNat},{attrKey a})"

mutual
/-- A key for an expression. -/
def exprKey : Csyntax.Expr → String
  | .Eval v ty => s!"Val({valKey v},{tyKey ty})"
  | .Evar x ty => s!"Var({x.toNat},{tyKey ty})"
  | .Efield l f ty => s!"Fld({exprKey l},{f.toNat},{tyKey ty})"
  | .Evalof l ty => s!"Vof({exprKey l},{tyKey ty})"
  | .Ederef r ty => s!"Drf({exprKey r},{tyKey ty})"
  | .Eaddrof l ty => s!"Adr({exprKey l},{tyKey ty})"
  | .Eunop op r ty => s!"Un({op.ctorIdx},{exprKey r},{tyKey ty})"
  | .Ebinop op r1 r2 ty => s!"Bin({op.ctorIdx},{exprKey r1},{exprKey r2},{tyKey ty})"
  | .Ecast r ty => s!"Cst({exprKey r},{tyKey ty})"
  | .Eseqand r1 r2 ty => s!"And({exprKey r1},{exprKey r2},{tyKey ty})"
  | .Eseqor r1 r2 ty => s!"Or({exprKey r1},{exprKey r2},{tyKey ty})"
  | .Econdition r1 r2 r3 ty => s!"Cnd({exprKey r1},{exprKey r2},{exprKey r3},{tyKey ty})"
  | .Esizeof ty' ty => s!"Sz({tyKey ty'},{tyKey ty})"
  | .Ealignof ty' ty => s!"Al({tyKey ty'},{tyKey ty})"
  | .Eassign l r ty => s!"Asg({exprKey l},{exprKey r},{tyKey ty})"
  | .Eassignop op l r tyres ty =>
    s!"Aop({op.ctorIdx},{exprKey l},{exprKey r},{tyKey tyres},{tyKey ty})"
  | .Epostincr id l ty => s!"Inc({id.ctorIdx},{exprKey l},{tyKey ty})"
  | .Ecomma r1 r2 ty => s!"Cma({exprKey r1},{exprKey r2},{tyKey ty})"
  | .Ecall r1 rargs ty => s!"Cal({exprKey r1},{exprlistKey rargs},{tyKey ty})"
  | .Ebuiltin ef tyargs rargs ty =>
    s!"Blt({reprStr ef},[{",".intercalate (tyargs.map tyKey)}],{exprlistKey rargs},{tyKey ty})"
  | .Eloc b ofs bf ty => s!"Loc({b.toNat},{ofs.toNat},{bitfieldKey bf},{tyKey ty})"
  | .Eparen r tycast ty => s!"Par({exprKey r},{tyKey tycast},{tyKey ty})"

/-- A key for a list of expressions. -/
def exprlistKey : Csyntax.ExprList → String
  | .Enil => "N"
  | .Econs r1 rl => s!"C({exprKey r1},{exprlistKey rl})"
end

mutual
/-- A key for a statement. -/
def stmtKey : Csyntax.Stmt → String
  | .Sskip => "skip"
  | .Sdo e => s!"do({exprKey e})"
  | .Ssequence s1 s2 => s!"seq({stmtKey s1},{stmtKey s2})"
  | .Sifthenelse e s1 s2 => s!"if({exprKey e},{stmtKey s1},{stmtKey s2})"
  | .Swhile e s => s!"while({exprKey e},{stmtKey s})"
  | .Sdowhile e s => s!"dowhile({exprKey e},{stmtKey s})"
  | .Sfor s1 e s2 s3 => s!"for({stmtKey s1},{exprKey e},{stmtKey s2},{stmtKey s3})"
  | .Sbreak => "break"
  | .Scontinue => "continue"
  | .Sreturn none => "ret"
  | .Sreturn (some e) => s!"ret({exprKey e})"
  | .Sswitch e ls => s!"switch({exprKey e},{lstmtsKey ls})"
  | .Slabel lbl s => s!"lbl({lbl.toNat},{stmtKey s})"
  | .Sgoto lbl => s!"goto({lbl.toNat})"

/-- A key for the cases of a `switch`. -/
def lstmtsKey : Csyntax.LStmts → String
  | .LSnil => "N"
  | .LScons c s ls => s!"C({reprStr c},{stmtKey s},{lstmtsKey ls})"
end

/-- A key for a function. -/
def functionKey (f : Csyntax.Function) : String :=
  let vars (l : List (Ident × Ty)) := ",".intercalate (l.map fun (x, t) => s!"{x.toNat}:{tyKey t}")
  s!"fn({tyKey f.fn_return},{ccKey f.fn_callconv},[{vars f.fn_params}],[{vars f.fn_vars}],{stmtKey f.fn_body})"

/-- A key for a function definition. -/
def fundefKey : Csyntax.FunDef → String
  | .Internal f => functionKey f
  | .External ef targs tres cc =>
    s!"ext({reprStr ef},[{",".intercalate (targs.map tyKey)}],{tyKey tres},{ccKey cc})"

/-- A key for a local environment. -/
def envKey (e : Env) : String :=
  ",".intercalate (PTree.elements e |>.map fun (x, (b, t)) => s!"{x.toNat}:{b.toNat}:{tyKey t}")

/-- A key for a memory: its contents (`compare_mem`) and its next block. -/
def memKey (m : Mem) : String :=
  let zmapKey (zm : ZMap MemVal) : String :=
    s!"{memvalKey zm.dflt}:[" ++
      ",".intercalate (PTree.elements zm.tree |>.map fun (i, v) => s!"{i.toNat}={memvalKey v}") ++ "]"
  let blocks := PTree.elements m.contents.tree |>.map fun (b, zm) => s!"{b.toNat}:{zmapKey zm}"
  s!"{m.nextblock.toNat};{zmapKey m.contents.dflt};" ++ ";".intercalate blocks

/-- `some_expr` -/
def someExpr : Csyntax.Expr := .Eval (.Vint Integers.Int.zero) .Tvoid

/-- A key for a continuation (`compare_cont`). -/
def contKey : Csem.Cont → String
  | .Kstop => "stop"
  | .Kdo k => s!"do;{contKey k}"
  | .Kseq s k => s!"seq({stmtKey s});{contKey k}"
  | .Kifthenelse s1 s2 k => s!"if({stmtKey s1},{stmtKey s2});{contKey k}"
  | .Kwhile1 x s k => s!"w1({exprKey x},{stmtKey s});{contKey k}"
  | .Kwhile2 x s k => s!"w2({exprKey x},{stmtKey s});{contKey k}"
  | .Kdowhile1 x s k => s!"d1({exprKey x},{stmtKey s});{contKey k}"
  | .Kdowhile2 x s k => s!"d2({exprKey x},{stmtKey s});{contKey k}"
  | .Kfor2 e2 e3 s k => s!"f2({exprKey e2},{stmtKey e3},{stmtKey s});{contKey k}"
  | .Kfor3 e2 e3 s k => s!"f3({exprKey e2},{stmtKey e3},{stmtKey s});{contKey k}"
  | .Kfor4 e2 e3 s k => s!"f4({exprKey e2},{stmtKey e3},{stmtKey s});{contKey k}"
  | .Kswitch1 ls k => s!"s1({lstmtsKey ls});{contKey k}"
  | .Kswitch2 k => s!"s2;{contKey k}"
  | .Kreturn k => s!"ret;{contKey k}"
  | .Kcall f e C ty k =>
    s!"call({functionKey f},{envKey e},{exprKey (C someExpr)},{tyKey ty});{contKey k}"

/-- A key for a state (`compare_state`). -/
def stateKey : Csem.State → String
  | .State f s k e m =>
    s!"S|{functionKey f}|{stmtKey s}|{envKey e}|{contKey k}|{memKey m}"
  | .ExprState f r k e m =>
    s!"E|{functionKey f}|{exprKey r}|{envKey e}|{contKey k}|{memKey m}"
  | .Callstate fd args k m =>
    s!"C|{fundefKey fd}|{valsKey args}|{contKey k}|{memKey m}"
  | .Returnstate res k m => s!"R|{valKey res}|{contKey k}|{memKey m}"
  | .Stuckstate => "stuck"

/-- `explore_all`: all executions, one generation of states at a time. -/
partial def exploreAll (cfg : Config) (prog : Csyntax.Program) (ge : Csem.CGenv)
    (time : Nat) (states : List (Nat × Csem.State × Mem)) : DM Unit := do
  stopIfCanceled
  if cfg.trace ≥ 2 then
    for (n, s, _) in states do
      io (printLine (txt s!"State {time}.{n}:" ++ ppf "@ " ++ printState prog s))
  let mut next : Array (Nat × Csem.State × Mem) := #[]
  let mut seen : Std.HashMap String Nat := {}
  let mut numseen := 1
  for (n, s, w) in states do
    for (r, s', w') in ← doStep cfg prog ge time s w do
      let k := stateKey s'
      let n' ← match seen.get? k with
        | some n' => pure n'
        | none => do
          next := next.push (numseen, s', w')
          seen := seen.insert k numseen
          numseen := numseen + 1
          pure (numseen - 1)
      if cfg.trace ≥ 2 then
        io (IO.println s!"Transition state {time}.{n} --[{r}]--> state {time + 1}.{n'}")
  if !next.isEmpty then exploreAll cfg prog ge (time + 1) next.toList

/-! ## Preparing the program -/

/-- `world_program`: volatile variables become ordinary variables (so that
    the world can read and write them), the other variables become empty. -/
def worldProgram (prog : Csyntax.Program) : Csyntax.Program :=
  { prog with prog_defs := prog.prog_defs.map fun (id, gd) =>
      match gd with
      | .Gvar gv =>
        if gv.gvar_volatile then (id, .Gvar { gv with gvar_readonly := false, gvar_volatile := false })
        else (id, .Gvar { gv with gvar_init := [] })
      | .Gfun _ => (id, gd) }

/-- `change_main_function` -/
def changeMainFunction (p : Csyntax.Program) (newMainFn : Csyntax.Function) : Csyntax.Program :=
  let newMainId := identOfString "%main%"
  { p with prog_main := newMainId,
           prog_defs := (newMainId, .Gfun (.Internal newMainFn)) :: p.prog_defs }

/-- `call_main3_function`: `return main(0, 0);` -/
def callMain3Function (mainId : Ident) (mainTy : Ty) : Csyntax.Function :=
  let mainVar := Expr.Evalof (.Evar mainId mainTy) mainTy
  let arg := Expr.Eval (.Vint (Integers.Int.repr 0)) type_int32s
  { fn_return := type_int32s, fn_callconv := cc_default, fn_params := [], fn_vars := []
    fn_body := .Sreturn (some (.Ecall mainVar (.Econs arg (.Econs arg .Enil)) type_int32s)) }

/-- `call_other_main_function`: `main(); return 0;` -/
def callOtherMainFunction (mainId : Ident) (mainTy mainTyRes : Ty) : Csyntax.Function :=
  let mainVar := Expr.Evalof (.Evar mainId mainTy) mainTy
  { fn_return := type_int32s, fn_callconv := cc_default, fn_params := [], fn_vars := []
    fn_body := .Ssequence (.Sdo (.Ecall mainVar .Enil mainTyRes))
      (.Sreturn (some (.Eval (.Vint (Integers.Int.repr 0)) type_int32s))) }

/-- `find_main_function` -/
def findMainFunction (name : Ident) : List (Ident × GlobDef Csyntax.FunDef Ty) →
    Option Csyntax.FunDef
  | [] => none
  | (id, .Gfun fd) :: gdl => if id == name then some fd else findMainFunction name gdl
  | (_, .Gvar _) :: gdl => findMainFunction name gdl

/-- `fixup_main`: make the entry point a function `int main(void)`. -/
def fixupMain (p : Csyntax.Program) : Except String Csyntax.Program :=
  match findMainFunction p.prog_main p.prog_defs with
  | none => .error s!"ERROR: no entry function {externAtom p.prog_main}()"
  | some mainFd =>
    match Csyntax.typeOfFundef mainFd with
    | .Tfunction [] (.Tint .I32 .Signed _) _ => .ok p
    | ty@(.Tfunction [.Tint _ _ _, .Tpointer (.Tpointer (.Tint .I8 _ _) _) _] (.Tint _ _ _) _) =>
      .ok (changeMainFunction p (callMain3Function p.prog_main ty))
    | ty@(.Tfunction [] tyRes _) =>
      .ok (changeMainFunction p (callOtherMainFunction p.prog_main ty tyRes))
    | _ => .error s!"ERROR: wrong type for entry function {externAtom p.prog_main}()"

/-! ## Execution of a whole program -/

/-- `execute prog` -/
def execute (prog : Csyntax.Program) : DM Unit := do
  let st ← get
  match fixupMain prog with
  | .error msg => io (IO.eprintln msg); throwThe Stop (.Exit 126)
  | .ok prog1 =>
    let wprog := worldProgram prog1
    let wge := Csem.globalenv wprog
    let cfg : Config := { trace := st.interp_trace, mode := st.interp_mode, wge }
    match Csem.initMem wprog with
    | none => io (IO.println "ERROR: World memory state undefined"); throwThe Stop (.Exit 126)
    | some wm =>
      match doInitialState prog1 with
      | none => io (IO.println "ERROR: Initial state undefined"); throwThe Stop (.Exit 126)
      | some (ge, s) =>
        match cfg.mode with
        | .First | .Random => exploreOne cfg prog1 ge 0 s wm
        | .All => exploreAll cfg prog1 ge 0 [(1, s, wm)]

end Interp
end CC
