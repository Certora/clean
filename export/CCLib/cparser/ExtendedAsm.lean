/-
  Port of `cparser/ExtendedAsm.ml`: partial emulation of GCC's extended
  inline assembly (experimental).

  `transf_asm` takes a full GCC-style extended asm statement and puts it in
  the form supported by CompCert: 0 or 1 output of kind "r", and inputs of
  kind "r".  Operands of kind "m" are emulated by taking their address;
  inputs of kind "i" and "n" are evaluated at compile time and substituted
  in the template.

  The target-specific functions `CBuiltins.asm_mem_argument`,
  `Machregsnames.register_by_name` and `Machregsaux.is_scratch_register`
  are the fields of the argument `tgt : TargetAsm`.  The regular
  expressions of OCaml's `Str` are replaced by hand-written scanners.
-/
import CCLib.cparser.Ceval

namespace CC
namespace CParser
namespace ExtendedAsm

open C Cutil Diagnostics

/-- The target-dependent functions used by this module. -/
structure TargetAsm where
  asm_mem_argument : String → String
  /-- `Machregsnames.register_by_name c <> None` -/
  is_register_name : String → Bool
  is_scratch_register : String → Bool

abbrev StringMap := Std.HashMap String String

def name_of_label (lbl : Option String) (pos : Int) (modifier : String := "") : String :=
  match lbl with
  | none => s!"%{modifier}{pos}"
  | some l => s!"%{modifier}[{l}]"

def set_label_reg (lbl : Option String) (pos pos' : Int) (subst : StringMap) : StringMap :=
  subst.insert (name_of_label lbl pos) s!"%{pos'}"

/-- `%Rxxx` / `%Qxxx`: most / least significant half of a register pair. -/
def set_label_regpair (lbl : Option String) (pos pos' : Int) (subst : StringMap) : StringMap :=
  (subst.insert (name_of_label lbl pos "Q") s!"%Q{pos'}").insert
    (name_of_label lbl pos "R") s!"%R{pos'}"

def set_label_mem (tgt : TargetAsm) (lbl : Option String) (pos pos' : Int)
    (subst : StringMap) : StringMap :=
  subst.insert (name_of_label lbl pos) (tgt.asm_mem_argument s!"%{pos'}")

def set_label_const (lbl : Option String) (pos : Int) (n : Int64) (subst : StringMap) :
    StringMap :=
  subst.insert (name_of_label lbl pos) (toString n.toInt)

/-- Operands of 64-bit integer type get split into a pair of registers on
    32-bit platforms -/
def is_reg_pair (env : Env.T) (ty : Typ) : M Bool := do
  match ← unroll env ty with
  | .TInt ik _ => return (← sizeof_ikind ik) > (← getConfig).sizeof_intreg
  | _ => return false

/-- `Str.string_match "[a-zA-Z]+$" s 0` -/
def valid_input (s : String) : Bool := !s.isEmpty && s.all Char.isAlpha

/-- `Str.string_match "=[a-zA-Z]+$" s 0` -/
def valid_output (s : String) : Bool :=
  s.startsWith "=" && valid_input (s.drop 1).toString

/-- Transform the input operands. -/
def transf_inputs (tgt : TargetAsm) (loc : Location) (env : Env.T) (accu : List Exp)
    (pos pos' : Int) (subst : StringMap) : List AsmOperand → M (List Exp × StringMap)
  | [] => return (accu.reverse, subst)
  | (lbl, cstr, e) :: inputs => do
      let valid := valid_input cstr
      if valid && cstr.contains 'r' then
        if ← is_reg_pair env e.etyp then
          transf_inputs tgt loc env (e :: accu) (pos + 1) (pos' + 1)
            (set_label_regpair lbl pos pos' subst) inputs
        else
          transf_inputs tgt loc env (e :: accu) (pos + 1) (pos' + 1)
            (set_label_reg lbl pos pos' subst) inputs
      else if valid && cstr.contains 'm' then
        transf_inputs tgt loc env (eaddrof e :: accu) (pos + 1) (pos' + 1)
          (set_label_mem tgt lbl pos pos' subst) inputs
      else if valid && (cstr.contains 'i' || cstr.contains 'n') then
        let n ← match ← Ceval.integer_expr env e with
          | some n => pure n
          | none => do
              error loc s!"asm argument of kind '{cstr}' is not a constant"
              pure 0
        transf_inputs tgt loc env accu (pos + 1) pos' (set_label_const lbl pos n subst) inputs
      else
        error loc s!"unsupported feature: asm argument of kind '{cstr}'"
        transf_inputs tgt loc env (e :: accu) (pos + 1) (pos' + 1)
          (set_label_reg lbl pos pos' subst) inputs

/-- Transform the output operands. -/
def transf_outputs (tgt : TargetAsm) (loc : Location) (env : Env.T) :
    List AsmOperand → M (Option Exp × List Exp × StringMap × Int × Int)
  | [] => return (none, [], {}, 0, 0)
  | [(lbl, cstr, e)] => do
      let valid := valid_output cstr
      if valid && cstr.contains 'r' then
        if ← is_reg_pair env e.etyp then
          return (some e, [], set_label_regpair lbl 0 0 {}, 1, 1)
        else return (some e, [], set_label_reg lbl 0 0 {}, 1, 1)
      else if valid && cstr.contains 'm' then
        return (none, [eaddrof e], set_label_mem tgt lbl 0 0 {}, 1, 1)
      else
        error loc s!"unsupported feature: asm result of kind '{cstr}'"
        return (none, [], set_label_reg lbl 0 0 {}, 1, 1)
  | outputs => do
      error loc "unsupported feature: asm statement with 2 or more outputs"
      let mut pos : Int := 0
      let mut subst : StringMap := {}
      for (lbl, _, _) in outputs do
        subst := set_label_reg lbl pos pos subst
        pos := pos + 1
      return (none, [], subst, pos, pos)

/-- Check the clobber list -/
def check_clobbers (tgt : TargetAsm) (loc : Location) (clob : List String) : M Unit :=
  clob.forM fun c => do
    if tgt.is_register_name c || tgt.is_scratch_register c || c == "memory" || c == "cc" then
      pure ()
    else error loc s!"unrecognized asm register clobber '{c}'"

/-- Recognize a placeholder `%[QR]?([0-9]+|\[[a-zA-Z_][a-zA-Z_0-9]*\])` or
    `%%` at the start of `cs`; returns its length. -/
def matchPlaceholder (cs : List Char) : Option Nat :=
  match cs with
  | '%' :: '%' :: _ => some 2
  | '%' :: rest =>
      let (m, rest) := match rest with
        | 'Q' :: r | 'R' :: r => (1, r)
        | r => (0, r)
      let isIdStart (c : Char) := c.isAlpha || c == '_'
      let isId (c : Char) := c.isAlphanum || c == '_'
      match rest with
      | c :: _ =>
          if c.isDigit then some (1 + m + (rest.takeWhile Char.isDigit).length)
          else if c == '[' then
            match rest.drop 1 with
            | d :: r =>
                if isIdStart d then
                  let n := (r.takeWhile isId).length
                  if (r.drop n).head? == some ']' then some (1 + m + 1 + 1 + n + 1) else none
                else none
            | [] => none
          else none
      | [] => none
  | _ => none

/-- Renaming of the `%nnn` and `%[ident]` placeholders in the asm text -/
def rename_placeholders (loc : Location) (template : String) (subst : StringMap) : M String := do
  let mut out := ""
  let mut cs := template.toList
  for _ in [0:template.length + 1] do
    match cs with
    | [] => break
    | c :: rest =>
      match matchPlaceholder cs with
      | some n =>
          let p := String.ofList (cs.take n)
          let r ← if p == "%%" then pure p else
            match subst.get? p with
            | some r => pure r
            | none => do
                error loc s!"'{p}' in asm text does not designate any operand"
                pure "%<error>"
          out := out ++ r
          cs := cs.drop n
      | none =>
          out := out.push c
          cs := rest
  return out

/-- All together -/
def transf_asm (tgt : TargetAsm) (loc : Location) (env : Env.T) (template : String)
    (outputs inputs : List AsmOperand) (clobbers : List String) :
    M (String × Option Exp × List Exp) := do
  let (outputs', inputs1, subst1, pos, pos') ← transf_outputs tgt loc env outputs
  let (inputs', subst) ← transf_inputs tgt loc env inputs1 pos pos' subst1 inputs
  check_clobbers tgt loc clobbers
  return (← rename_placeholders loc template subst, outputs', inputs')

end ExtendedAsm
end CParser
end CC
