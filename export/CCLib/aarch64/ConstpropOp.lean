/-
  Strength reduction for operators and conditions (the machine-dependent
  part of constant propagation) — port of `aarch64/ConstpropOp.vp`
  (definitions).

  Ported: `const_for_result`, `eval_static_shift`, `eval_static_shiftl`,
  `eval_static_extend` (on concrete integers), `cond_strength_reduction`,
  `make_cmp_base`, `make_cmp_imm_eq`, `make_cmp_imm_ne`, `make_cmp`,
  `make_select`, `make_addimm`, `make_shlimm`, `make_shrimm`,
  `make_shruimm`, `make_mulimm`, `make_andimm`, `make_orimm`,
  `make_xorimm`, `make_divimm`, `make_divuimm`, `make_addlimm`,
  `make_shllimm`, `make_shrlimm`, `make_shrluimm`, `make_mullimm`,
  `make_andlimm`, `make_orlimm`, `make_xorlimm`, `make_divlimm`,
  `make_divluimm`, `make_mulfimm`, `make_mulfsimm`, `make_zext`,
  `make_sext`, `op_strength_reduction`, `addr_strength_reduction`.
  Not ported: `ConstpropOpproof.v`.

  Differences from Rocq: `Nondetfunction` definitions are ordinary
  first-match `match`es; the guard `?? negb (symbol_is_relocatable symb)`
  of `addr_strength_reduction` is an `if` (no later case applies when it
  fails).  The OCaml parameters `Compopts.generate_float_constants`,
  `SelectOp.symbol_is_relocatable` (and those of `ValueAOp.Options`) are
  fields of `ConstpropOp.Options`.
-/
import CCLib.aarch64.ValueAOp
import CCLib.aarch64.SelectOp
import CCLib.backend.RTL

namespace CC
namespace ConstpropOp

open ValueDomain Op

/-- The compiler options used by constant propagation. -/
structure Options extends ValueAOp.Options where
  /-- `Compopts.generate_float_constants` -/
  generateFloatConstants : Bool := true
  /-- `SelectOp.symbol_is_relocatable` -/
  symbolIsRelocatable : Ident → Bool := fun _ => false

/-- `ConstpropOp.const_for_result` -/
def constForResult (o : Options) (a : Aval) : Option Operation :=
  match a with
  | .I n | .IU n => some (.Ointconst n)
  | .L n => some (.Olongconst n)
  | .F n => if o.generateFloatConstants then some (.Ofloatconst n) else none
  | .FS n => if o.generateFloatConstants then some (.Osingleconst n) else none
  | .Ptr (.Gl id ofs) => some (.Oaddrsymbol id ofs)
  | .Ptr (.Stk ofs) => some (.Oaddrstack ofs)
  | _ => none

/-- `ConstpropOp.eval_static_shift` -/
def evalStaticShift (s : Shift) (v : Integers.Int) (n : Amount32) : Integers.Int :=
  match s with
  | .Slsl => Integers.Int.shl v n.a32_amount
  | .Slsr => Integers.Int.shru v n.a32_amount
  | .Sasr => Integers.Int.shr v n.a32_amount
  | .Sror => Integers.Int.ror v n.a32_amount

/-- `ConstpropOp.eval_static_shiftl` -/
def evalStaticShiftl (s : Shift) (v : Integers.Int64) (n : Amount64) : Integers.Int64 :=
  match s with
  | .Slsl => Integers.Int64.shl' v n.a64_amount
  | .Slsr => Integers.Int64.shru' v n.a64_amount
  | .Sasr => Integers.Int64.shr' v n.a64_amount
  | .Sror => Integers.Int64.ror v (Integers.Int64.repr (Integers.Int.unsigned n.a64_amount))

/-- `ConstpropOp.eval_static_extend` -/
def evalStaticExtend (x : Extension) (v : Integers.Int) (n : Amount64) : Integers.Int64 :=
  Integers.Int64.shl'
    (match x with
     | .Xsgn32 => Integers.Int64.repr (Integers.Int.signed v)
     | .Xuns32 => Integers.Int64.repr (Integers.Int.unsigned v))
    n.a64_amount

/-- `ConstpropOp.cond_strength_reduction` -/
def condStrengthReduction (cond : Condition) (args : List Reg) (vl : List Aval) :
    Condition × List Reg :=
  match cond, args, vl with
  | .Ccomp c, [_, r2], [.I n1, _] => (.Ccompimm c.swap n1, [r2])
  | .Ccomp c, [r1, _], [_, .I n2] => (.Ccompimm c n2, [r1])
  | .Ccompu c, [_, r2], [.I n1, _] => (.Ccompuimm c.swap n1, [r2])
  | .Ccompu c, [r1, _], [_, .I n2] => (.Ccompuimm c n2, [r1])
  | .Ccompshift c s a, [r1, _], [_, .I n2] => (.Ccompimm c (evalStaticShift s n2 a), [r1])
  | .Ccompushift c s a, [r1, _], [_, .I n2] => (.Ccompuimm c (evalStaticShift s n2 a), [r1])
  | .Ccompl c, [_, r2], [.L n1, _] => (.Ccomplimm c.swap n1, [r2])
  | .Ccompl c, [r1, _], [_, .L n2] => (.Ccomplimm c n2, [r1])
  | .Ccomplu c, [_, r2], [.L n1, _] => (.Ccompluimm c.swap n1, [r2])
  | .Ccomplu c, [r1, _], [_, .L n2] => (.Ccompluimm c n2, [r1])
  | .Ccomplshift c s a, [r1, _], [_, .L n2] => (.Ccomplimm c (evalStaticShiftl s n2 a), [r1])
  | .Ccomplushift c s a, [r1, _], [_, .L n2] => (.Ccompluimm c (evalStaticShiftl s n2 a), [r1])
  | .Ccompf c, [_, r2], [.F n1, _] =>
      if n1 = Floats.Float.zero then (.Ccompfzero c.swap, [r2]) else (cond, args)
  | .Ccompf c, [r1, _], [_, .F n2] =>
      if n2 = Floats.Float.zero then (.Ccompfzero c, [r1]) else (cond, args)
  | .Cnotcompf c, [_, r2], [.F n1, _] =>
      if n1 = Floats.Float.zero then (.Cnotcompfzero c.swap, [r2]) else (cond, args)
  | .Cnotcompf c, [r1, _], [_, .F n2] =>
      if n2 = Floats.Float.zero then (.Cnotcompfzero c, [r1]) else (cond, args)
  | .Ccompfs c, [_, r2], [.FS n1, _] =>
      if n1 = Floats.Float32.zero then (.Ccompfszero c.swap, [r2]) else (cond, args)
  | .Ccompfs c, [r1, _], [_, .FS n2] =>
      if n2 = Floats.Float32.zero then (.Ccompfszero c, [r1]) else (cond, args)
  | .Cnotcompfs c, [_, r2], [.FS n1, _] =>
      if n1 = Floats.Float32.zero then (.Cnotcompfszero c.swap, [r2]) else (cond, args)
  | .Cnotcompfs c, [r1, _], [_, .FS n2] =>
      if n2 = Floats.Float32.zero then (.Cnotcompfszero c, [r1]) else (cond, args)
  | _, _, _ => (cond, args)

/-- `ConstpropOp.make_cmp_base` -/
def makeCmpBase (c : Condition) (args : List Reg) (vl : List Aval) : Operation × List Reg :=
  let (c', args') := condStrengthReduction c args vl
  (.Ocmp c', args')

/-- `ConstpropOp.make_cmp_imm_eq` -/
def makeCmpImmEq (c : Condition) (args : List Reg) (vl : List Aval) (n : Integers.Int) (r1 : Reg)
    (v1 : Aval) : Operation × List Reg :=
  if decide (n = Integers.Int.one) && vincl v1 (.Uns .Ptop 1) then (.Omove, [r1])
  else if decide (n = Integers.Int.zero) && vincl v1 (.Uns .Ptop 1) then
    (.Oxorimm Integers.Int.one, [r1])
  else makeCmpBase c args vl

/-- `ConstpropOp.make_cmp_imm_ne` -/
def makeCmpImmNe (c : Condition) (args : List Reg) (vl : List Aval) (n : Integers.Int) (r1 : Reg)
    (v1 : Aval) : Operation × List Reg :=
  if decide (n = Integers.Int.zero) && vincl v1 (.Uns .Ptop 1) then (.Omove, [r1])
  else if decide (n = Integers.Int.one) && vincl v1 (.Uns .Ptop 1) then
    (.Oxorimm Integers.Int.one, [r1])
  else makeCmpBase c args vl

/-- `ConstpropOp.make_cmp` -/
def makeCmp (c : Condition) (args : List Reg) (vl : List Aval) : Operation × List Reg :=
  match c, args, vl with
  | .Ccompimm .Ceq n, [r1], [v1] => makeCmpImmEq c args vl n r1 v1
  | .Ccompimm .Cne n, [r1], [v1] => makeCmpImmNe c args vl n r1 v1
  | .Ccompuimm .Ceq n, [r1], [v1] => makeCmpImmEq c args vl n r1 v1
  | .Ccompuimm .Cne n, [r1], [v1] => makeCmpImmNe c args vl n r1 v1
  | _, _, _ => makeCmpBase c args vl

/-- `ConstpropOp.make_select` -/
def makeSelect (o : Options) (c : Condition) (ty : ATyp) (r1 r2 : Reg) (args : List Reg)
    (vl : List Aval) : Operation × List Reg :=
  match resolveBranch (ValueAOp.evalStaticCondition o.toOptions c vl) with
  | some b => (.Omove, [if b then r1 else r2])
  | none =>
      let (c', args') := condStrengthReduction c args vl
      (.Osel c' ty, r1 :: r2 :: args')

/-- `ConstpropOp.make_addimm` -/
def makeAddimm (n : Integers.Int) (r : Reg) : Operation × List Reg :=
  if Integers.Int.eq n Integers.Int.zero then (.Omove, [r]) else (.Oaddimm n, [r])

/-- `ConstpropOp.make_shlimm` -/
def makeShlimm (n : Integers.Int) (r1 r2 : Reg) : Operation × List Reg :=
  if Integers.Int.eq n Integers.Int.zero then (.Omove, [r1])
  else if Integers.Int.ltu n Integers.Int.iwordsize then (.Oshift .Slsl (mkAmount32 n), [r1])
  else (.Oshl, [r1, r2])

/-- `ConstpropOp.make_shrimm` -/
def makeShrimm (n : Integers.Int) (r1 r2 : Reg) : Operation × List Reg :=
  if Integers.Int.eq n Integers.Int.zero then (.Omove, [r1])
  else if Integers.Int.ltu n Integers.Int.iwordsize then (.Oshift .Sasr (mkAmount32 n), [r1])
  else (.Oshr, [r1, r2])

/-- `ConstpropOp.make_shruimm` -/
def makeShruimm (n : Integers.Int) (r1 r2 : Reg) : Operation × List Reg :=
  if Integers.Int.eq n Integers.Int.zero then (.Omove, [r1])
  else if Integers.Int.ltu n Integers.Int.iwordsize then (.Oshift .Slsr (mkAmount32 n), [r1])
  else (.Oshru, [r1, r2])

/-- `ConstpropOp.make_mulimm` -/
def makeMulimm (n : Integers.Int) (r1 r2 : Reg) : Operation × List Reg :=
  if Integers.Int.eq n Integers.Int.zero then (.Ointconst Integers.Int.zero, [])
  else if Integers.Int.eq n Integers.Int.one then (.Omove, [r1])
  else
    match Integers.Int.is_power2 n with
    | some l => (.Oshift .Slsl (mkAmount32 l), [r1])
    | none => (.Omul, [r1, r2])

/-- `ConstpropOp.make_andimm` -/
def makeAndimm (n : Integers.Int) (r : Reg) (a : Aval) : Operation × List Reg :=
  if Integers.Int.eq n Integers.Int.zero then (.Ointconst Integers.Int.zero, [])
  else if Integers.Int.eq n Integers.Int.mone then (.Omove, [r])
  else if (match a with
      | .Uns _ m => Integers.Int.eq (Integers.Int.zero_ext m.toNat (Integers.Int.not n))
          Integers.Int.zero
      | _ => false)
  then (.Omove, [r])
  else (.Oandimm n, [r])

/-- `ConstpropOp.make_orimm` -/
def makeOrimm (n : Integers.Int) (r : Reg) : Operation × List Reg :=
  if Integers.Int.eq n Integers.Int.zero then (.Omove, [r])
  else if Integers.Int.eq n Integers.Int.mone then (.Ointconst Integers.Int.mone, [])
  else (.Oorimm n, [r])

/-- `ConstpropOp.make_xorimm` -/
def makeXorimm (n : Integers.Int) (r : Reg) : Operation × List Reg :=
  if Integers.Int.eq n Integers.Int.zero then (.Omove, [r]) else (.Oxorimm n, [r])

/-- `ConstpropOp.make_divimm` -/
def makeDivimm (n : Integers.Int) (r1 r2 : Reg) : Operation × List Reg :=
  if Integers.Int.eq n Integers.Int.one then (.Omove, [r1])
  else
    match Integers.Int.is_power2 n with
    | some l =>
        if Integers.Int.ltu l (Integers.Int.repr 31) then (.Oshrximm l, [r1]) else (.Odiv, [r1, r2])
    | none => (.Odiv, [r1, r2])

/-- `ConstpropOp.make_divuimm` -/
def makeDivuimm (n : Integers.Int) (r1 r2 : Reg) : Operation × List Reg :=
  if Integers.Int.eq n Integers.Int.one then (.Omove, [r1])
  else
    match Integers.Int.is_power2 n with
    | some l => (.Oshift .Slsr (mkAmount32 l), [r1])
    | none => (.Odivu, [r1, r2])

/-- `ConstpropOp.make_addlimm` -/
def makeAddlimm (n : Integers.Int64) (r : Reg) : Operation × List Reg :=
  if Integers.Int64.eq n Integers.Int64.zero then (.Omove, [r]) else (.Oaddlimm n, [r])

/-- `ConstpropOp.make_shllimm` -/
def makeShllimm (n : Integers.Int) (r1 r2 : Reg) : Operation × List Reg :=
  if Integers.Int.eq n Integers.Int.zero then (.Omove, [r1])
  else if Integers.Int.ltu n Integers.Int64.iwordsize' then (.Oshiftl .Slsl (mkAmount64 n), [r1])
  else (.Oshll, [r1, r2])

/-- `ConstpropOp.make_shrlimm` -/
def makeShrlimm (n : Integers.Int) (r1 r2 : Reg) : Operation × List Reg :=
  if Integers.Int.eq n Integers.Int.zero then (.Omove, [r1])
  else if Integers.Int.ltu n Integers.Int64.iwordsize' then (.Oshiftl .Sasr (mkAmount64 n), [r1])
  else (.Oshrl, [r1, r2])

/-- `ConstpropOp.make_shrluimm` -/
def makeShrluimm (n : Integers.Int) (r1 r2 : Reg) : Operation × List Reg :=
  if Integers.Int.eq n Integers.Int.zero then (.Omove, [r1])
  else if Integers.Int.ltu n Integers.Int64.iwordsize' then (.Oshiftl .Slsr (mkAmount64 n), [r1])
  else (.Oshrlu, [r1, r2])

/-- `ConstpropOp.make_mullimm` -/
def makeMullimm (n : Integers.Int64) (r1 r2 : Reg) : Operation × List Reg :=
  if Integers.Int64.eq n Integers.Int64.zero then (.Olongconst Integers.Int64.zero, [])
  else if Integers.Int64.eq n Integers.Int64.one then (.Omove, [r1])
  else
    match Integers.Int64.is_power2' n with
    | some l => (.Oshiftl .Slsl (mkAmount64 l), [r1])
    | none => (.Omull, [r1, r2])

/-- `ConstpropOp.make_andlimm` -/
def makeAndlimm (n : Integers.Int64) (r : Reg) (_a : Aval) : Operation × List Reg :=
  if Integers.Int64.eq n Integers.Int64.zero then (.Olongconst Integers.Int64.zero, [])
  else if Integers.Int64.eq n Integers.Int64.mone then (.Omove, [r])
  else (.Oandlimm n, [r])

/-- `ConstpropOp.make_orlimm` -/
def makeOrlimm (n : Integers.Int64) (r : Reg) : Operation × List Reg :=
  if Integers.Int64.eq n Integers.Int64.zero then (.Omove, [r])
  else if Integers.Int64.eq n Integers.Int64.mone then (.Olongconst Integers.Int64.mone, [])
  else (.Oorlimm n, [r])

/-- `ConstpropOp.make_xorlimm` -/
def makeXorlimm (n : Integers.Int64) (r : Reg) : Operation × List Reg :=
  if Integers.Int64.eq n Integers.Int64.zero then (.Omove, [r]) else (.Oxorlimm n, [r])

/-- `ConstpropOp.make_divlimm` -/
def makeDivlimm (n : Integers.Int64) (r1 r2 : Reg) : Operation × List Reg :=
  match Integers.Int64.is_power2' n with
  | some l =>
      if Integers.Int.ltu l (Integers.Int.repr 63) then (.Oshrlximm l, [r1]) else (.Odivl, [r1, r2])
  | none => (.Odivl, [r1, r2])

/-- `ConstpropOp.make_divluimm` -/
def makeDivluimm (n : Integers.Int64) (r1 r2 : Reg) : Operation × List Reg :=
  match Integers.Int64.is_power2' n with
  | some l => (.Oshiftl .Slsr (mkAmount64 l), [r1])
  | none => (.Odivlu, [r1, r2])

/-- `ConstpropOp.make_mulfimm` -/
def makeMulfimm (n : Floats.Float) (r r1 r2 : Reg) : Operation × List Reg :=
  if n = Floats.Float.ofInt (Integers.Int.repr 2) then (.Oaddf, [r, r]) else (.Omulf, [r1, r2])

/-- `ConstpropOp.make_mulfsimm` -/
def makeMulfsimm (n : Floats.Float32) (r r1 r2 : Reg) : Operation × List Reg :=
  if n = Floats.Float32.ofInt (Integers.Int.repr 2) then (.Oaddfs, [r, r])
  else (.Omulfs, [r1, r2])

/-- `ConstpropOp.make_zext` -/
def makeZext (s : Z) (r : Reg) (a : Aval) : Operation × List Reg :=
  if vincl a (.Uns .Ptop s) then (.Omove, [r]) else (.Ozext s, [r])

/-- `ConstpropOp.make_sext` -/
def makeSext (s : Z) (r : Reg) (a : Aval) : Operation × List Reg :=
  if vincl a (.Sgn .Ptop s) then (.Omove, [r]) else (.Osext s, [r])

/-- `ConstpropOp.op_strength_reduction`.  The Rocq function is one flat match on
    `(op, args, vl)`; here it is a match on `op` whose cases match on `(args, vl)`,
    with the same cases in the same order and the same default `(op, args)`. -/
def opStrengthReduction (o : Options) (op : Operation) (args : List Reg) (vl : List Aval) :
    Operation × List Reg :=
  match op with
  | .Oadd =>
      match args, vl with
      | [_, r2], [.I n1, _] => makeAddimm n1 r2
      | [r1, _], [_, .I n2] => makeAddimm n2 r1
      | _, _ => (op, args)
  | .Oaddshift s a =>
      match args, vl with
      | [r1, _], [_, .I n2] => makeAddimm (evalStaticShift s n2 a) r1
      | _, _ => (op, args)
  | .Osub =>
      match args, vl with
      | [r1, _], [_, .I n2] => makeAddimm (Integers.Int.neg n2) r1
      | _, _ => (op, args)
  | .Osubshift s a =>
      match args, vl with
      | [r1, _], [_, .I n2] => makeAddimm (Integers.Int.neg (evalStaticShift s n2 a)) r1
      | _, _ => (op, args)
  | .Omul =>
      match args, vl with
      | [r1, r2], [.I n1, _] => makeMulimm n1 r2 r1
      | [r1, r2], [_, .I n2] => makeMulimm n2 r1 r2
      | _, _ => (op, args)
  | .Odiv =>
      match args, vl with
      | [r1, r2], [_, .I n2] => makeDivimm n2 r1 r2
      | _, _ => (op, args)
  | .Odivu =>
      match args, vl with
      | [r1, r2], [_, .I n2] => makeDivuimm n2 r1 r2
      | _, _ => (op, args)
  | .Oand =>
      match args, vl with
      | [_, r2], [.I n1, v2] => makeAndimm n1 r2 v2
      | [r1, _], [v1, .I n2] => makeAndimm n2 r1 v1
      | _, _ => (op, args)
  | .Oandshift s a =>
      match args, vl with
      | [r1, _], [v1, .I n2] => makeAndimm (evalStaticShift s n2 a) r1 v1
      | _, _ => (op, args)
  | .Oandimm n =>
      match args, vl with
      | [r1], [v1] => makeAndimm n r1 v1
      | _, _ => (op, args)
  | .Oor =>
      match args, vl with
      | [_, r2], [.I n1, _] => makeOrimm n1 r2
      | [r1, _], [_, .I n2] => makeOrimm n2 r1
      | _, _ => (op, args)
  | .Oorshift s a =>
      match args, vl with
      | [r1, _], [_, .I n2] => makeOrimm (evalStaticShift s n2 a) r1
      | _, _ => (op, args)
  | .Oxor =>
      match args, vl with
      | [_, r2], [.I n1, _] => makeXorimm n1 r2
      | [r1, _], [_, .I n2] => makeXorimm n2 r1
      | _, _ => (op, args)
  | .Oxorshift s a =>
      match args, vl with
      | [r1, _], [_, .I n2] => makeXorimm (evalStaticShift s n2 a) r1
      | _, _ => (op, args)
  | .Obic =>
      match args, vl with
      | [r1, _], [v1, .I n2] => makeAndimm (Integers.Int.not n2) r1 v1
      | _, _ => (op, args)
  | .Obicshift s a =>
      match args, vl with
      | [r1, _], [v1, .I n2] => makeAndimm (Integers.Int.not (evalStaticShift s n2 a)) r1 v1
      | _, _ => (op, args)
  | .Oorn =>
      match args, vl with
      | [r1, _], [_, .I n2] => makeOrimm (Integers.Int.not n2) r1
      | _, _ => (op, args)
  | .Oornshift s a =>
      match args, vl with
      | [r1, _], [_, .I n2] => makeOrimm (Integers.Int.not (evalStaticShift s n2 a)) r1
      | _, _ => (op, args)
  | .Oeqv =>
      match args, vl with
      | [r1, _], [_, .I n2] => makeXorimm (Integers.Int.not n2) r1
      | _, _ => (op, args)
  | .Oeqvshift s a =>
      match args, vl with
      | [r1, _], [_, .I n2] => makeXorimm (Integers.Int.not (evalStaticShift s n2 a)) r1
      | _, _ => (op, args)
  | .Oshl =>
      match args, vl with
      | [r1, r2], [_, .I n2] => makeShlimm n2 r1 r2
      | _, _ => (op, args)
  | .Oshr =>
      match args, vl with
      | [r1, r2], [_, .I n2] => makeShrimm n2 r1 r2
      | _, _ => (op, args)
  | .Oshru =>
      match args, vl with
      | [r1, r2], [_, .I n2] => makeShruimm n2 r1 r2
      | _, _ => (op, args)
  | .Ozext s =>
      match args, vl with
      | [r1], [v1] => makeZext s r1 v1
      | _, _ => (op, args)
  | .Osext s =>
      match args, vl with
      | [r1], [v1] => makeSext s r1 v1
      | _, _ => (op, args)
  | .Oaddl =>
      match args, vl with
      | [_, r2], [.L n1, _] => makeAddlimm n1 r2
      | [r1, _], [_, .L n2] => makeAddlimm n2 r1
      | _, _ => (op, args)
  | .Oaddlshift s a =>
      match args, vl with
      | [r1, _], [_, .L n2] => makeAddlimm (evalStaticShiftl s n2 a) r1
      | _, _ => (op, args)
  | .Oaddlext x a =>
      match args, vl with
      | [r1, _], [_, .I n2] => makeAddlimm (evalStaticExtend x n2 a) r1
      | _, _ => (op, args)
  | .Osubl =>
      match args, vl with
      | [r1, _], [_, .L n2] => makeAddlimm (Integers.Int64.neg n2) r1
      | _, _ => (op, args)
  | .Osublshift s a =>
      match args, vl with
      | [r1, _], [_, .L n2] => makeAddlimm (Integers.Int64.neg (evalStaticShiftl s n2 a)) r1
      | _, _ => (op, args)
  | .Osublext x a =>
      match args, vl with
      | [r1, _], [_, .I n2] => makeAddlimm (Integers.Int64.neg (evalStaticExtend x n2 a)) r1
      | _, _ => (op, args)
  | .Omull =>
      match args, vl with
      | [r1, r2], [.L n1, _] => makeMullimm n1 r2 r1
      | [r1, r2], [_, .L n2] => makeMullimm n2 r1 r2
      | _, _ => (op, args)
  | .Odivl =>
      match args, vl with
      | [r1, r2], [_, .L n2] => makeDivlimm n2 r1 r2
      | _, _ => (op, args)
  | .Odivlu =>
      match args, vl with
      | [r1, r2], [_, .L n2] => makeDivluimm n2 r1 r2
      | _, _ => (op, args)
  | .Oandl =>
      match args, vl with
      | [_, r2], [.L n1, v2] => makeAndlimm n1 r2 v2
      | [r1, _], [v1, .L n2] => makeAndlimm n2 r1 v1
      | _, _ => (op, args)
  | .Oandlshift s a =>
      match args, vl with
      | [r1, _], [v1, .L n2] => makeAndlimm (evalStaticShiftl s n2 a) r1 v1
      | _, _ => (op, args)
  | .Oandlimm n =>
      match args, vl with
      | [r1], [v1] => makeAndlimm n r1 v1
      | _, _ => (op, args)
  | .Oorl =>
      match args, vl with
      | [_, r2], [.L n1, _] => makeOrlimm n1 r2
      | [r1, _], [_, .L n2] => makeOrlimm n2 r1
      | _, _ => (op, args)
  | .Oorlshift s a =>
      match args, vl with
      | [r1, _], [_, .L n2] => makeOrlimm (evalStaticShiftl s n2 a) r1
      | _, _ => (op, args)
  | .Oxorl =>
      match args, vl with
      | [_, r2], [.L n1, _] => makeXorlimm n1 r2
      | [r1, _], [_, .L n2] => makeXorlimm n2 r1
      | _, _ => (op, args)
  | .Oxorlshift s a =>
      match args, vl with
      | [r1, _], [_, .L n2] => makeXorlimm (evalStaticShiftl s n2 a) r1
      | _, _ => (op, args)
  | .Obicl =>
      match args, vl with
      | [r1, _], [v1, .L n2] => makeAndlimm (Integers.Int64.not n2) r1 v1
      | _, _ => (op, args)
  | .Obiclshift s a =>
      match args, vl with
      | [r1, _], [v1, .L n2] => makeAndlimm (Integers.Int64.not (evalStaticShiftl s n2 a)) r1 v1
      | _, _ => (op, args)
  | .Oornl =>
      match args, vl with
      | [r1, _], [_, .L n2] => makeOrlimm (Integers.Int64.not n2) r1
      | _, _ => (op, args)
  | .Oornlshift s a =>
      match args, vl with
      | [r1, _], [_, .L n2] => makeOrlimm (Integers.Int64.not (evalStaticShiftl s n2 a)) r1
      | _, _ => (op, args)
  | .Oeqvl =>
      match args, vl with
      | [r1, _], [_, .L n2] => makeXorlimm (Integers.Int64.not n2) r1
      | _, _ => (op, args)
  | .Oeqvlshift s a =>
      match args, vl with
      | [r1, _], [_, .L n2] => makeXorlimm (Integers.Int64.not (evalStaticShiftl s n2 a)) r1
      | _, _ => (op, args)
  | .Oshll =>
      match args, vl with
      | [r1, r2], [_, .I n2] => makeShllimm n2 r1 r2
      | _, _ => (op, args)
  | .Oshrl =>
      match args, vl with
      | [r1, r2], [_, .I n2] => makeShrlimm n2 r1 r2
      | _, _ => (op, args)
  | .Oshrlu =>
      match args, vl with
      | [r1, r2], [_, .I n2] => makeShrluimm n2 r1 r2
      | _, _ => (op, args)
  | .Ocmp c =>
      makeCmp c args vl
  | .Osel c ty =>
      match args, vl with
      | r1 :: r2 :: args, _ :: _ :: vl => makeSelect o c ty r1 r2 args vl
      | _, _ => (op, args)
  | .Omulf =>
      match args, vl with
      | [r1, r2], [_, .F n2] => makeMulfimm n2 r1 r1 r2
      | [r1, r2], [.F n1, _] => makeMulfimm n1 r2 r1 r2
      | _, _ => (op, args)
  | .Omulfs =>
      match args, vl with
      | [r1, r2], [_, .FS n2] => makeMulfsimm n2 r1 r1 r2
      | [r1, r2], [.FS n1, _] => makeMulfsimm n1 r2 r1 r2
      | _, _ => (op, args)
  | _ => (op, args)

/-- `ConstpropOp.addr_strength_reduction` -/
def addrStrengthReduction (o : Options) (addr : Addressing) (args : List Reg) (vl : List Aval) :
    Addressing × List Reg :=
  match addr, args, vl with
  | .Aindexed n, [_], [.Ptr (.Gl symb n1)] =>
      if !(o.symbolIsRelocatable symb) then
        (.Aglobal symb (Integers.Ptrofs.add n1 (Integers.Ptrofs.of_int64 n)), [])
      else (addr, args)
  | .Aindexed n, [_], [.Ptr (.Stk n1)] =>
      (.Ainstack (Integers.Ptrofs.add n1 (Integers.Ptrofs.of_int64 n)), [])
  | .Aindexed2, [_, _], [.Ptr (.Stk n1), .L n2] =>
      (.Ainstack (Integers.Ptrofs.add n1 (Integers.Ptrofs.of_int64 n2)), [])
  | .Aindexed2, [_, _], [.L n1, .Ptr (.Stk n2)] =>
      (.Ainstack (Integers.Ptrofs.add (Integers.Ptrofs.of_int64 n1) n2), [])
  | .Aindexed2, [_, r2], [.L n1, _] => (.Aindexed n1, [r2])
  | .Aindexed2, [r1, _], [_, .L n2] => (.Aindexed n2, [r1])
  | .Aindexed2shift a, [_, _], [.Ptr (.Stk n1), .L n2] =>
      (.Ainstack (Integers.Ptrofs.add n1
        (Integers.Ptrofs.of_int64 (Integers.Int64.shl' n2 a.a64_amount))), [])
  | .Aindexed2shift a, [r1, _], [_, .L n2] =>
      (.Aindexed (Integers.Int64.shl' n2 a.a64_amount), [r1])
  | .Aindexed2ext x a, [_, _], [.Ptr (.Stk n1), .I n2] =>
      (.Ainstack (Integers.Ptrofs.add n1 (Integers.Ptrofs.of_int64 (evalStaticExtend x n2 a))), [])
  | .Aindexed2ext x a, [r1, _], [_, .I n2] => (.Aindexed (evalStaticExtend x n2 a), [r1])
  | _, _, _ => (addr, args)

end ConstpropOp
end CC
