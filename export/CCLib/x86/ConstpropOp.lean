/-
  Strength reduction for operators and conditions (the machine-dependent
  part of constant propagation) for the x86 back end — port of
  `x86/ConstpropOp.vp` (definitions).

  Ported: `Olea_ptr`, `const_for_result`, `cond_strength_reduction`,
  `make_cmp_base`, `make_cmp_imm_eq`, `make_cmp_imm_ne`, `make_cmp`,
  `make_select`, `addr_strength_reduction_32_generic`,
  `addr_strength_reduction_32`, `addr_strength_reduction_64_generic`,
  `addr_strength_reduction_64`, `addr_strength_reduction`, `make_addimm`,
  `make_shlimm`, `make_shrimm`, `make_shruimm`, `make_mulimm`,
  `make_andimm`, `make_orimm`, `make_xorimm`, `make_divimm`,
  `make_divuimm`, `make_moduimm`, `make_addlimm`, `make_shllimm`,
  `make_shrlimm`, `make_shrluimm`, `make_mullimm`, `make_andlimm`,
  `make_orlimm`, `make_xorlimm`, `make_divlimm`, `make_divluimm`,
  `make_modluimm`, `make_mulfimm`, `make_mulfsimm`, `make_cast8signed`,
  `make_cast8unsigned`, `make_cast16signed`, `make_cast16unsigned`,
  `op_strength_reduction`.
  The soundness proofs are in `CCLib/x86/ConstpropOpproof.lean`.

  Differences from Rocq: `Nondetfunction` definitions are ordinary
  first-match `match`es (as in `CCLib/aarch64/ConstpropOp.lean`).  The OCaml
  parameters `Compopts.generate_float_constants` and
  `SelectOp.symbol_is_relocatable` (and those of `ValueAOp.Options`) are
  fields of `ConstpropOp.Options`; the structure is shared with the aarch64
  port.
-/
import CCLib.x86.ValueAOp
import CCLib.aarch64.ConstpropOp

namespace CC
namespace X86
namespace ConstpropOp

open ValueDomain Op
open CC.ConstpropOp (Options)

/-- `ConstpropOp.Olea_ptr` -/
def oleaPtr (a : Addressing) : Operation := if Archi.ptr64 then .Oleal a else .Olea a

/-- `ConstpropOp.const_for_result` -/
def constForResult (o : Options) (a : Aval) : Option Operation :=
  match a with
  | .I n | .IU n => some (.Ointconst n)
  | .L n => if Archi.ptr64 then some (.Olongconst n) else none
  | .F n => if o.generateFloatConstants then some (.Ofloatconst n) else none
  | .FS n => if o.generateFloatConstants then some (.Osingleconst n) else none
  | .Ptr (.Gl id ofs) =>
      if o.symbolIsRelocatable id then
        if Integers.Ptrofs.eq ofs Integers.Ptrofs.zero then some (.Oindirectsymbol id) else none
      else some (oleaPtr (.Aglobal id ofs))
  | .Ptr (.Stk ofs) => some (oleaPtr (.Ainstack ofs))
  | _ => none

/-- `ConstpropOp.cond_strength_reduction` -/
def condStrengthReduction (cond : Condition) (args : List Reg) (vl : List Aval) :
    Condition × List Reg :=
  match cond, args, vl with
  | .Ccomp c, [_, r2], [.I n1, _] => (.Ccompimm c.swap n1, [r2])
  | .Ccomp c, [r1, _], [_, .I n2] => (.Ccompimm c n2, [r1])
  | .Ccompu c, [_, r2], [.I n1, _] => (.Ccompuimm c.swap n1, [r2])
  | .Ccompu c, [r1, _], [_, .I n2] => (.Ccompuimm c n2, [r1])
  | .Ccompl c, [_, r2], [.L n1, _] => (.Ccomplimm c.swap n1, [r2])
  | .Ccompl c, [r1, _], [_, .L n2] => (.Ccomplimm c n2, [r1])
  | .Ccomplu c, [_, r2], [.L n1, _] => (.Ccompluimm c.swap n1, [r2])
  | .Ccomplu c, [r1, _], [_, .L n2] => (.Ccompluimm c n2, [r1])
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

/-- `ConstpropOp.addr_strength_reduction_32_generic` -/
def addrStrengthReduction32Generic (addr : Addressing) (args : List Reg) (vl : List Aval) :
    Addressing × List Reg :=
  match addr, args, vl with
  | .Aindexed2 ofs, [_, r2], [.I n1, _] => (.Aindexed (Integers.Int.signed n1 + ofs), [r2])
  | .Aindexed2 ofs, [r1, _], [_, .I n2] => (.Aindexed (Integers.Int.signed n2 + ofs), [r1])
  | .Aindexed2scaled sc ofs, [r1, _], [_, .I n2] =>
      (.Aindexed (Integers.Int.signed n2 * sc + ofs), [r1])
  | .Aindexed2scaled sc ofs, [_, r2], [.I n1, _] =>
      (.Ascaled sc (Integers.Int.signed n1 + ofs), [r2])
  | _, _, _ => (addr, args)

/-- `ConstpropOp.addr_strength_reduction_32` -/
def addrStrengthReduction32 (addr : Addressing) (args : List Reg) (vl : List Aval) :
    Addressing × List Reg :=
  if Archi.ptr64 then addrStrengthReduction32Generic addr args vl else
  match addr, args, vl with
  | .Aindexed ofs, [_], [.Ptr (.Gl symb n)] =>
      (.Aglobal symb (Integers.Ptrofs.add n (Integers.Ptrofs.repr ofs)), [])
  | .Aindexed ofs, [_], [.Ptr (.Stk n)] =>
      (.Ainstack (Integers.Ptrofs.add n (Integers.Ptrofs.repr ofs)), [])
  | .Aindexed2 ofs, [_, _], [.Ptr (.Gl symb n1), .I n2] =>
      (.Aglobal symb (Integers.Ptrofs.add (Integers.Ptrofs.add n1 (Integers.Ptrofs.of_int n2))
        (Integers.Ptrofs.repr ofs)), [])
  | .Aindexed2 ofs, [_, _], [.I n1, .Ptr (.Gl symb n2)] =>
      (.Aglobal symb (Integers.Ptrofs.add (Integers.Ptrofs.add n2 (Integers.Ptrofs.of_int n1))
        (Integers.Ptrofs.repr ofs)), [])
  | .Aindexed2 ofs, [_, _], [.Ptr (.Stk n1), .I n2] =>
      (.Ainstack (Integers.Ptrofs.add (Integers.Ptrofs.add n1 (Integers.Ptrofs.of_int n2))
        (Integers.Ptrofs.repr ofs)), [])
  | .Aindexed2 ofs, [_, _], [.I n1, .Ptr (.Stk n2)] =>
      (.Ainstack (Integers.Ptrofs.add (Integers.Ptrofs.add (Integers.Ptrofs.of_int n1) n2)
        (Integers.Ptrofs.repr ofs)), [])
  | .Aindexed2 ofs, [_, r2], [.Ptr (.Gl symb n1), _] =>
      (.Abased symb (Integers.Ptrofs.add n1 (Integers.Ptrofs.repr ofs)), [r2])
  | .Aindexed2 ofs, [r1, _], [_, .Ptr (.Gl symb n2)] =>
      (.Abased symb (Integers.Ptrofs.add n2 (Integers.Ptrofs.repr ofs)), [r1])
  | .Aindexed2scaled sc ofs, [_, _], [.Ptr (.Gl symb n1), .I n2] =>
      (.Aglobal symb (Integers.Ptrofs.add (Integers.Ptrofs.add n1
        (Integers.Ptrofs.of_int (Integers.Int.mul n2 (Integers.Int.repr sc))))
        (Integers.Ptrofs.repr ofs)), [])
  | .Aindexed2scaled sc ofs, [_, r2], [.Ptr (.Gl symb n1), _] =>
      (.Abasedscaled sc symb (Integers.Ptrofs.add n1 (Integers.Ptrofs.repr ofs)), [r2])
  | .Abased id ofs, [_], [.I n1] =>
      (.Aglobal id (Integers.Ptrofs.add ofs (Integers.Ptrofs.of_int n1)), [])
  | .Abasedscaled sc id ofs, [_], [.I n1] =>
      (.Aglobal id (Integers.Ptrofs.add ofs
        (Integers.Ptrofs.of_int (Integers.Int.mul n1 (Integers.Int.repr sc)))), [])
  | _, _, _ => addrStrengthReduction32Generic addr args vl

/-- `ConstpropOp.addr_strength_reduction_64_generic` -/
def addrStrengthReduction64Generic (addr : Addressing) (args : List Reg) (vl : List Aval) :
    Addressing × List Reg :=
  match addr, args, vl with
  | .Aindexed2 ofs, [_, r2], [.L n1, _] => (.Aindexed (Integers.Int64.signed n1 + ofs), [r2])
  | .Aindexed2 ofs, [r1, _], [_, .L n2] => (.Aindexed (Integers.Int64.signed n2 + ofs), [r1])
  | .Aindexed2scaled sc ofs, [r1, _], [_, .L n2] =>
      (.Aindexed (Integers.Int64.signed n2 * sc + ofs), [r1])
  | .Aindexed2scaled sc ofs, [_, r2], [.L n1, _] =>
      (.Ascaled sc (Integers.Int64.signed n1 + ofs), [r2])
  | _, _, _ => (addr, args)

/-- `ConstpropOp.addr_strength_reduction_64` -/
def addrStrengthReduction64 (addr : Addressing) (args : List Reg) (vl : List Aval) :
    Addressing × List Reg :=
  if !Archi.ptr64 then addrStrengthReduction64Generic addr args vl else
  match addr, args, vl with
  | .Aindexed ofs, [_], [.Ptr (.Gl symb n)] =>
      (.Aglobal symb (Integers.Ptrofs.add n (Integers.Ptrofs.repr ofs)), [])
  | .Aindexed ofs, [_], [.Ptr (.Stk n)] =>
      (.Ainstack (Integers.Ptrofs.add n (Integers.Ptrofs.repr ofs)), [])
  | .Aindexed2 ofs, [_, _], [.Ptr (.Gl symb n1), .L n2] =>
      (.Aglobal symb (Integers.Ptrofs.add (Integers.Ptrofs.add n1 (Integers.Ptrofs.of_int64 n2))
        (Integers.Ptrofs.repr ofs)), [])
  | .Aindexed2 ofs, [_, _], [.L n1, .Ptr (.Gl symb n2)] =>
      (.Aglobal symb (Integers.Ptrofs.add (Integers.Ptrofs.add n2 (Integers.Ptrofs.of_int64 n1))
        (Integers.Ptrofs.repr ofs)), [])
  | .Aindexed2 ofs, [_, _], [.Ptr (.Stk n1), .L n2] =>
      (.Ainstack (Integers.Ptrofs.add (Integers.Ptrofs.add n1 (Integers.Ptrofs.of_int64 n2))
        (Integers.Ptrofs.repr ofs)), [])
  | .Aindexed2 ofs, [_, _], [.L n1, .Ptr (.Stk n2)] =>
      (.Ainstack (Integers.Ptrofs.add (Integers.Ptrofs.add (Integers.Ptrofs.of_int64 n1) n2)
        (Integers.Ptrofs.repr ofs)), [])
  | .Aindexed2scaled sc ofs, [_, _], [.Ptr (.Gl symb n1), .L n2] =>
      (.Aglobal symb (Integers.Ptrofs.add (Integers.Ptrofs.add n1
        (Integers.Ptrofs.of_int64 (Integers.Int64.mul n2 (Integers.Int64.repr sc))))
        (Integers.Ptrofs.repr ofs)), [])
  | _, _, _ => addrStrengthReduction64Generic addr args vl

/-- `ConstpropOp.addr_strength_reduction` -/
def addrStrengthReduction (addr : Addressing) (args : List Reg) (vl : List Aval) :
    Addressing × List Reg :=
  let addrArgs' :=
    if Archi.ptr64 then addrStrengthReduction64 addr args vl
    else addrStrengthReduction32 addr args vl
  if addressingValid addrArgs'.1 then addrArgs' else (addr, args)

/-- `ConstpropOp.make_addimm` -/
def makeAddimm (n : Integers.Int) (r : Reg) : Operation × List Reg :=
  if Integers.Int.eq n Integers.Int.zero then (.Omove, [r])
  else (.Olea (.Aindexed (Integers.Int.signed n)), [r])

/-- `ConstpropOp.make_shlimm` -/
def makeShlimm (n : Integers.Int) (r1 r2 : Reg) : Operation × List Reg :=
  if Integers.Int.eq n Integers.Int.zero then (.Omove, [r1])
  else if Integers.Int.ltu n Integers.Int.iwordsize then (.Oshlimm n, [r1])
  else (.Oshl, [r1, r2])

/-- `ConstpropOp.make_shrimm` -/
def makeShrimm (n : Integers.Int) (r1 r2 : Reg) : Operation × List Reg :=
  if Integers.Int.eq n Integers.Int.zero then (.Omove, [r1])
  else if Integers.Int.ltu n Integers.Int.iwordsize then (.Oshrimm n, [r1])
  else (.Oshr, [r1, r2])

/-- `ConstpropOp.make_shruimm` -/
def makeShruimm (n : Integers.Int) (r1 r2 : Reg) : Operation × List Reg :=
  if Integers.Int.eq n Integers.Int.zero then (.Omove, [r1])
  else if Integers.Int.ltu n Integers.Int.iwordsize then (.Oshruimm n, [r1])
  else (.Oshru, [r1, r2])

/-- `ConstpropOp.make_mulimm` -/
def makeMulimm (n : Integers.Int) (r : Reg) : Operation × List Reg :=
  if Integers.Int.eq n Integers.Int.zero then (.Ointconst Integers.Int.zero, [])
  else if Integers.Int.eq n Integers.Int.one then (.Omove, [r])
  else
    match Integers.Int.is_power2 n with
    | some l => (.Oshlimm l, [r])
    | none => (.Omulimm n, [r])

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
  if Integers.Int.eq n Integers.Int.zero then (.Omove, [r])
  else if Integers.Int.eq n Integers.Int.mone then (.Onot, [r])
  else (.Oxorimm n, [r])

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
    | some l => (.Oshruimm l, [r1])
    | none => (.Odivu, [r1, r2])

/-- `ConstpropOp.make_moduimm` -/
def makeModuimm (n : Integers.Int) (r1 r2 : Reg) : Operation × List Reg :=
  match Integers.Int.is_power2 n with
  | some _ => (.Oandimm (Integers.Int.sub n Integers.Int.one), [r1])
  | none => (.Omodu, [r1, r2])

/-- `ConstpropOp.make_addlimm` -/
def makeAddlimm (n : Integers.Int64) (r : Reg) : Operation × List Reg :=
  if Integers.Int64.eq n Integers.Int64.zero then (.Omove, [r])
  else (.Oleal (.Aindexed (Integers.Int64.signed n)), [r])

/-- `ConstpropOp.make_shllimm` -/
def makeShllimm (n : Integers.Int) (r1 r2 : Reg) : Operation × List Reg :=
  if Integers.Int.eq n Integers.Int.zero then (.Omove, [r1])
  else if Integers.Int.ltu n Integers.Int64.iwordsize' then (.Oshllimm n, [r1])
  else (.Oshll, [r1, r2])

/-- `ConstpropOp.make_shrlimm` -/
def makeShrlimm (n : Integers.Int) (r1 r2 : Reg) : Operation × List Reg :=
  if Integers.Int.eq n Integers.Int.zero then (.Omove, [r1])
  else if Integers.Int.ltu n Integers.Int64.iwordsize' then (.Oshrlimm n, [r1])
  else (.Oshrl, [r1, r2])

/-- `ConstpropOp.make_shrluimm` -/
def makeShrluimm (n : Integers.Int) (r1 r2 : Reg) : Operation × List Reg :=
  if Integers.Int.eq n Integers.Int.zero then (.Omove, [r1])
  else if Integers.Int.ltu n Integers.Int64.iwordsize' then (.Oshrluimm n, [r1])
  else (.Oshrlu, [r1, r2])

/-- `ConstpropOp.make_mullimm` -/
def makeMullimm (n : Integers.Int64) (r : Reg) : Operation × List Reg :=
  if Integers.Int64.eq n Integers.Int64.zero then (.Olongconst Integers.Int64.zero, [])
  else if Integers.Int64.eq n Integers.Int64.one then (.Omove, [r])
  else
    match Integers.Int64.is_power2' n with
    | some l => (.Oshllimm l, [r])
    | none => (.Omullimm n, [r])

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
  if Integers.Int64.eq n Integers.Int64.zero then (.Omove, [r])
  else if Integers.Int64.eq n Integers.Int64.mone then (.Onotl, [r])
  else (.Oxorlimm n, [r])

/-- `ConstpropOp.make_divlimm` -/
def makeDivlimm (n : Integers.Int64) (r1 r2 : Reg) : Operation × List Reg :=
  match Integers.Int64.is_power2' n with
  | some l =>
      if Integers.Int.ltu l (Integers.Int.repr 63) then (.Oshrxlimm l, [r1]) else (.Odivl, [r1, r2])
  | none => (.Odivl, [r1, r2])

/-- `ConstpropOp.make_divluimm` -/
def makeDivluimm (n : Integers.Int64) (r1 r2 : Reg) : Operation × List Reg :=
  match Integers.Int64.is_power2' n with
  | some l => (.Oshrluimm l, [r1])
  | none => (.Odivlu, [r1, r2])

/-- `ConstpropOp.make_modluimm` -/
def makeModluimm (n : Integers.Int64) (r1 r2 : Reg) : Operation × List Reg :=
  match Integers.Int64.is_power2 n with
  | some _ => (.Oandlimm (Integers.Int64.sub n Integers.Int64.one), [r1])
  | none => (.Omodlu, [r1, r2])

/-- `ConstpropOp.make_mulfimm` -/
def makeMulfimm (n : Floats.Float) (r r1 r2 : Reg) : Operation × List Reg :=
  if n = Floats.Float.ofInt (Integers.Int.repr 2) then (.Oaddf, [r, r]) else (.Omulf, [r1, r2])

/-- `ConstpropOp.make_mulfsimm` -/
def makeMulfsimm (n : Floats.Float32) (r r1 r2 : Reg) : Operation × List Reg :=
  if n = Floats.Float32.ofInt (Integers.Int.repr 2) then (.Oaddfs, [r, r])
  else (.Omulfs, [r1, r2])

/-- `ConstpropOp.make_cast8signed` -/
def makeCast8signed (r : Reg) (a : Aval) : Operation × List Reg :=
  if vincl a (.Sgn .Ptop 8) then (.Omove, [r]) else (.Ocast8signed, [r])

/-- `ConstpropOp.make_cast8unsigned` -/
def makeCast8unsigned (r : Reg) (a : Aval) : Operation × List Reg :=
  if vincl a (.Uns .Ptop 8) then (.Omove, [r]) else (.Ocast8unsigned, [r])

/-- `ConstpropOp.make_cast16signed` -/
def makeCast16signed (r : Reg) (a : Aval) : Operation × List Reg :=
  if vincl a (.Sgn .Ptop 16) then (.Omove, [r]) else (.Ocast16signed, [r])

/-- `ConstpropOp.make_cast16unsigned` -/
def makeCast16unsigned (r : Reg) (a : Aval) : Operation × List Reg :=
  if vincl a (.Uns .Ptop 16) then (.Omove, [r]) else (.Ocast16unsigned, [r])

/-- `ConstpropOp.op_strength_reduction`.  The Rocq function is one flat match on
    `(op, args, vl)`; here it is a match on `op` whose cases match on `(args, vl)`,
    with the same cases in the same order and the same default `(op, args)`. -/
def opStrengthReduction (o : Options) (op : Operation) (args : List Reg) (vl : List Aval) :
    Operation × List Reg :=
  match op with
  | .Ocast8signed =>
      match args, vl with
      | [r1], [v1] => makeCast8signed r1 v1
      | _, _ => (op, args)
  | .Ocast8unsigned =>
      match args, vl with
      | [r1], [v1] => makeCast8unsigned r1 v1
      | _, _ => (op, args)
  | .Ocast16signed =>
      match args, vl with
      | [r1], [v1] => makeCast16signed r1 v1
      | _, _ => (op, args)
  | .Ocast16unsigned =>
      match args, vl with
      | [r1], [v1] => makeCast16unsigned r1 v1
      | _, _ => (op, args)
  | .Osub =>
      match args, vl with
      | [r1, _], [_, .I n2] => makeAddimm (Integers.Int.neg n2) r1
      | _, _ => (op, args)
  | .Omul =>
      match args, vl with
      | [_, r2], [.I n1, _] => makeMulimm n1 r2
      | [r1, _], [_, .I n2] => makeMulimm n2 r1
      | _, _ => (op, args)
  | .Odiv =>
      match args, vl with
      | [r1, r2], [_, .I n2] => makeDivimm n2 r1 r2
      | _, _ => (op, args)
  | .Odivu =>
      match args, vl with
      | [r1, r2], [_, .I n2] => makeDivuimm n2 r1 r2
      | _, _ => (op, args)
  | .Omodu =>
      match args, vl with
      | [r1, r2], [_, .I n2] => makeModuimm n2 r1 r2
      | _, _ => (op, args)
  | .Oand =>
      match args, vl with
      | [_, r2], [.I n1, v2] => makeAndimm n1 r2 v2
      | [r1, _], [v1, .I n2] => makeAndimm n2 r1 v1
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
  | .Oxor =>
      match args, vl with
      | [_, r2], [.I n1, _] => makeXorimm n1 r2
      | [r1, _], [_, .I n2] => makeXorimm n2 r1
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
  | .Olea addr =>
      let (addr', args') := addrStrengthReduction32 addr args vl
      (.Olea addr', args')
  | .Osubl =>
      match args, vl with
      | [r1, _], [_, .L n2] => makeAddlimm (Integers.Int64.neg n2) r1
      | _, _ => (op, args)
  | .Omull =>
      match args, vl with
      | [_, r2], [.L n1, _] => makeMullimm n1 r2
      | [r1, _], [_, .L n2] => makeMullimm n2 r1
      | _, _ => (op, args)
  | .Odivl =>
      match args, vl with
      | [r1, r2], [_, .L n2] => makeDivlimm n2 r1 r2
      | _, _ => (op, args)
  | .Odivlu =>
      match args, vl with
      | [r1, r2], [_, .L n2] => makeDivluimm n2 r1 r2
      | _, _ => (op, args)
  | .Omodlu =>
      match args, vl with
      | [r1, r2], [_, .L n2] => makeModluimm n2 r1 r2
      | _, _ => (op, args)
  | .Oandl =>
      match args, vl with
      | [_, r2], [.L n1, v2] => makeAndlimm n1 r2 v2
      | [r1, _], [v1, .L n2] => makeAndlimm n2 r1 v1
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
  | .Oxorl =>
      match args, vl with
      | [_, r2], [.L n1, _] => makeXorlimm n1 r2
      | [r1, _], [_, .L n2] => makeXorlimm n2 r1
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
  | .Oleal addr =>
      let (addr', args') := addrStrengthReduction64 addr args vl
      (.Oleal addr', args')
  | .Ocmp c => makeCmp c args vl
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

end ConstpropOp
end X86
end CC
