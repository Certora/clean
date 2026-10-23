/-
  Recognition of combined operations (used by common subexpression
  elimination) — port of `aarch64/CombineOp.v`: `combine_compimm_ne_0`,
  `combine_compimm_eq_0`, `combine_compimm_eq_1`, `combine_compimm_ne_1`,
  `combine_cond`, `combine_cond'`, `combine_addr`, `combine_op`.
  The soundness proofs are in `CCLib/aarch64/CombineOpproof.lean`.
-/
import CCLib.backend.CSEdomain

namespace CC

namespace CombineOp

open CSEdomain Op

section COMBINE
variable (get : Valnum → Option Rhs)

/-- `CombineOp.combine_compimm_ne_0` -/
def combineCompimmNe0 (x : Valnum) : Option (Condition × List Valnum) :=
  match get x with
  | some (.Op (.Ocmp c) ys) => some (c, ys)
  | some (.Op (.Oxorimm n) ys) =>
      if Integers.Int.eq n (Integers.Int.zero_ext 12 n) then some (.Ccompimm .Cne n, ys) else none
  | _ => none

/-- `CombineOp.combine_compimm_eq_0` -/
def combineCompimmEq0 (x : Valnum) : Option (Condition × List Valnum) :=
  match get x with
  | some (.Op (.Ocmp c) ys) => some (negateCondition c, ys)
  | some (.Op (.Oxorimm n) ys) =>
      if Integers.Int.eq n (Integers.Int.zero_ext 12 n) then some (.Ccompimm .Ceq n, ys) else none
  | _ => none

/-- `CombineOp.combine_compimm_eq_1` -/
def combineCompimmEq1 (x : Valnum) : Option (Condition × List Valnum) :=
  match get x with
  | some (.Op (.Ocmp c) ys) => some (c, ys)
  | _ => none

/-- `CombineOp.combine_compimm_ne_1` -/
def combineCompimmNe1 (x : Valnum) : Option (Condition × List Valnum) :=
  match get x with
  | some (.Op (.Ocmp c) ys) => some (negateCondition c, ys)
  | _ => none

/-- Shared body of the `Cne` cases of `combine_cond`. -/
def combineNe (n : Integers.Int) (x : Valnum) : Option (Condition × List Valnum) :=
  if n = Integers.Int.zero then combineCompimmNe0 get x
  else if n = Integers.Int.one then combineCompimmNe1 get x
  else none

/-- Shared body of the `Ceq` cases of `combine_cond`. -/
def combineEq (n : Integers.Int) (x : Valnum) : Option (Condition × List Valnum) :=
  if n = Integers.Int.zero then combineCompimmEq0 get x
  else if n = Integers.Int.one then combineCompimmEq1 get x
  else none

/-- `CombineOp.combine_cond` -/
def combineCond (cond : Condition) (args : List Valnum) : Option (Condition × List Valnum) :=
  match cond, args with
  | .Ccompimm .Cne n, [x] => combineNe get n x
  | .Ccompimm .Ceq n, [x] => combineEq get n x
  | .Ccompuimm .Cne n, [x] => combineNe get n x
  | .Ccompuimm .Ceq n, [x] => combineEq get n x
  | _, _ => none

end COMBINE

/-- `CombineOp.combine_cond'` -/
def combineCond' (cond : Condition) (args : List Valnum) : Option Bool :=
  match cond, args with
  | .Ccomp c, [x, y] | .Ccompu c, [x, y] | .Ccompl c, [x, y] | .Ccomplu c, [x, y] =>
      combineComparison c x y
  | _, _ => none

section COMBINE
variable (get : Valnum → Option Rhs)

/-- `CombineOp.combine_addr` -/
def combineAddr (addr : Addressing) (args : List Valnum) : Option (Addressing × List Valnum) :=
  match addr, args with
  | .Aindexed n, [x] =>
      match get x with
      | some (.Op (.Oaddlimm m) ys) => some (.Aindexed (Integers.Int64.add m n), ys)
      | _ => none
  | _, _ => none

/-- `CombineOp.combine_op` -/
def combineOp (op : Operation) (args : List Valnum) : Option (Operation × List Valnum) :=
  match op, args with
  | .Oaddimm n, [x] =>
      match get x with
      | some (.Op (.Oaddimm m) ys) => some (.Oaddimm (Integers.Int.add m n), ys)
      | _ => none
  | .Oandimm n, [x] =>
      match get x with
      | some (.Op (.Oandimm m) ys) =>
          some (let p := Integers.Int.and m n
                if Integers.Int.eq p m then (.Omove, [x]) else (.Oandimm p, ys))
      | _ => none
  | .Oorimm n, [x] =>
      match get x with
      | some (.Op (.Oorimm m) ys) => some (.Oorimm (Integers.Int.or m n), ys)
      | _ => none
  | .Oxorimm n, [x] =>
      match get x with
      | some (.Op (.Oxorimm m) ys) => some (.Oxorimm (Integers.Int.xor m n), ys)
      | _ => none
  | .Oaddlimm n, [x] =>
      match get x with
      | some (.Op (.Oaddlimm m) ys) => some (.Oaddlimm (Integers.Int64.add m n), ys)
      | _ => none
  | .Oandlimm n, [x] =>
      match get x with
      | some (.Op (.Oandlimm m) ys) =>
          some (let p := Integers.Int64.and m n
                if Integers.Int64.eq p m then (.Omove, [x]) else (.Oandlimm p, ys))
      | _ => none
  | .Oorlimm n, [x] =>
      match get x with
      | some (.Op (.Oorlimm m) ys) => some (.Oorlimm (Integers.Int64.or m n), ys)
      | _ => none
  | .Oxorlimm n, [x] =>
      match get x with
      | some (.Op (.Oxorlimm m) ys) => some (.Oxorlimm (Integers.Int64.xor m n), ys)
      | _ => none
  | .Ocmp cond, _ =>
      match combineCond' cond args with
      | some b => some ((if b then .Ointconst Integers.Int.one else .Ointconst Integers.Int.zero), [])
      | none =>
          match combineCond get cond args with
          | some (cond', args') => some (.Ocmp cond', args')
          | none => none
  | .Osel cond ty, x :: y :: args =>
      match combineCond' cond args with
      | some b => some (.Omove, [if b then x else y])
      | none =>
          if x = y then some (.Omove, [x])
          else
            match combineCond get cond args with
            | some (cond', args') => some (.Osel cond' ty, x :: y :: args')
            | none => none
  | _, _ => none

end COMBINE

end CombineOp
end CC
